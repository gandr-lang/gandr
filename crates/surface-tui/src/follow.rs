//! The side view: a render-bus client that follows the document the hub
//! checked last and shows its cards, its account and the context stack at its
//! cursor, beside an editor that shows the text, and the activity pane of the
//! hub's pool below them.
//!
//! The view builds the frame of the document it follows
//! ([`Following::frame`]): one record that names the document, its version
//! and its counts, then one record per declaration of the account, then one
//! record per card and per hole. So a card that comes or goes moves no row of
//! the account. The stack pane follows: one record per spine at the cursor,
//! the innermost first, its type with the parameter of the cursor's slot
//! underlined. The activity pane comes last: one record per core of the pool,
//! then the totals record. [`rendering`] lays the frame out as the
//! visual language's rendering data, which every rule of
//! `gandr_surface_render_remote::RULES` checks. A painter then puts the cells
//! on the terminal or on a pipe and adds nothing: a column is as wide as its
//! widest cell, one space parts two columns, and a hue takes the theme's
//! colour for its warrant. The terminal keeps the activity pane at the foot of
//! the screen, so a long report never pushes it out of view. A pipe prints the
//! document alone, because a pipe only appends and a live pane changes in
//! place: the stack pane moves with the cursor.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::time::Duration;
use std::io;
use std::io::BufRead;
use std::io::Write;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;
use std::sync::mpsc::channel;
use std::thread;

use anodized::spec;
use gandr_surface_render_remote::AccountCard;
use gandr_surface_render_remote::Align;
use gandr_surface_render_remote::Attribute;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::Cell;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::Datum;
use gandr_surface_render_remote::DiagnosticCode;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::DocumentUri;
use gandr_surface_render_remote::Field;
use gandr_surface_render_remote::FieldName;
use gandr_surface_render_remote::Frame;
use gandr_surface_render_remote::FrameBody;
use gandr_surface_render_remote::FrameScope;
use gandr_surface_render_remote::Head;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::Load;
use gandr_surface_render_remote::MarkKind;
use gandr_surface_render_remote::Numeral;
use gandr_surface_render_remote::Pane;
use gandr_surface_render_remote::Place;
use gandr_surface_render_remote::PoolActivity;
use gandr_surface_render_remote::Record;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_render_remote::Rendering;
use gandr_surface_render_remote::ReportView;
use gandr_surface_render_remote::Revision;
use gandr_surface_render_remote::Row;
use gandr_surface_render_remote::SampleUnit;
use gandr_surface_render_remote::SourceText;
use gandr_surface_render_remote::Sparkline;
use gandr_surface_render_remote::StackCard;
use gandr_surface_render_remote::Unit;
use gandr_surface_render_remote::WARRANTS;
use gandr_surface_render_remote::Warrant;
use gandr_surface_render_remote::apply_account_edits;
use gandr_surface_repl::Ended;
use gandr_surface_repl::Fault;
use ratatui::Terminal;
use ratatui::backend::Backend;
use ratatui::layout::Constraint;
use ratatui::layout::Layout;
use ratatui::style::Modifier;
use ratatui::style::Style;
use ratatui::text::Line;
use ratatui::text::Span;
use ratatui::widgets::Paragraph;

use crate::app::Key;
use crate::run::Input;
use crate::run::InputSource as _;
use crate::run::Keyboard;
use crate::theme::hue_of_warrant;

/// The name of the field that names the document: the first field of the
/// record that the side view draws as names beside their data.
const DOCUMENT: &str = "uri";

/// What the side view knows: the last report, the account and the stack card
/// of each document it heard, which one the hub checked last, and the last
/// activity of the hub's pool.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Following
{
    /// The last report heard for each document, with the version it reports.
    reports: BTreeMap<DocumentUri, (DocId, ReportView)>,
    /// The account cards held for each document, with the version of the last
    /// account frame.
    accounts: BTreeMap<DocumentUri, (DocId, Vec<AccountCard>)>,
    /// The last stack card heard for each document, with the version it was
    /// read at.
    stacks: BTreeMap<DocumentUri, (DocId, StackCard)>,
    /// The document whose report arrived last.
    latest: Option<DocumentUri>,
    /// The activity of the hub's pool that arrived last.
    activity: Option<PoolActivity>,
}

/// What hearing a frame leaves the view to do.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Heard
{
    /// Draw and wait for the next frame.
    Continue,
    /// The hub closed the bus.
    Detached,
}

/// One cell as a painter puts it on a line: its text, padded to its column's
/// width, and the cell it draws, which names its attributes; a head draws no
/// cell.
pub type Painted<'pane> = (String, Option<&'pane Cell>);

impl Following
{
    /// Take in `frame`, one the hub sent.
    ///
    /// # Specification
    /// - ensures: a report replaces the one held for its document and makes
    ///   that document the one followed. The account held for the document is
    ///   then current at the report's version, because the bus sends a change
    ///   of the account before its report. A whole account replaces the cards
    ///   held for its document, and a patch applies to them, and neither
    ///   changes the document followed. A stack card replaces the one held for
    ///   its document and changes nothing else. An activity frame replaces the
    ///   activity held. A detach answers [`Heard::Detached`] and changes
    ///   nothing; a greeting and a resync change nothing.
    /// - provides: the view's one update step.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reports of two documents, one after the other, leave
    ///   the second followed; a newer report of the first follows it again with
    ///   its new version; a detach is reported. A whole account and a patch
    ///   leave the cards that the patch names, a later report leaves them
    ///   current, and an account older than the report shows in the pending
    ///   hue. A stack card shows the stack pane. An activity frame shows the
    ///   pool's pane.
    /// - witness: `follow::tests::the_view_follows_the_document_checked_last`
    /// - witness: `follow::tests::the_view_shows_one_row_per_declaration_of_the_account`
    /// - witness: `follow::tests::the_view_shows_the_activity_of_the_pool`
    /// - witness: `follow::tests::the_view_shows_the_stack_at_the_cursor`
    #[spec(ensures: |ret| matches!(ret, Heard::Continue | Heard::Detached))]
    #[inline]
    pub fn hear(
        &mut self,
        frame: &RenderFrame,
    ) -> Heard
    {
        match (frame.scope(), frame.body()) {
            (&FrameScope::Document(ref document), &FrameBody::Frame { ref report }) => {
                drop(
                    self.reports
                        .insert(document.uri.clone(), (document.clone(), report.clone())),
                );
                self.latest = Some(document.uri.clone());
                // The bus sends a change of the account before the report it
                // goes with, so the account held is current at the report's
                // version.
                if let Some(&mut (ref mut accounted, _)) = self.accounts.get_mut(&document.uri)
                    && accounted.version < document.version
                {
                    accounted.clone_from(document);
                }
                Heard::Continue
            },
            (&FrameScope::Document(ref document), &FrameBody::Accounts { ref cards }) => {
                drop(
                    self.accounts
                        .insert(document.uri.clone(), (document.clone(), cards.clone())),
                );
                Heard::Continue
            },
            (&FrameScope::Document(ref document), &FrameBody::AccountPatch { ref edits }) => {
                let &mut (ref mut version, ref mut cards) = self
                    .accounts
                    .entry(document.uri.clone())
                    .or_insert_with(|| (document.clone(), Vec::new()));
                version.clone_from(document);
                apply_account_edits(cards, edits.clone());
                Heard::Continue
            },
            (&FrameScope::Document(ref document), &FrameBody::Stack { ref card }) => {
                drop(
                    self.stacks
                        .insert(document.uri.clone(), (document.clone(), card.clone())),
                );
                Heard::Continue
            },
            (_, &FrameBody::Activity { ref activity }) => {
                self.activity = Some(activity.clone());
                Heard::Continue
            },
            (_, &FrameBody::Detach) => Heard::Detached,
            (
                _,
                &(FrameBody::Hello { .. }
                | FrameBody::Frame { .. }
                | FrameBody::Resync
                | FrameBody::Accounts { .. }
                | FrameBody::AccountPatch { .. }
                | FrameBody::Stack { .. }),
            ) => Heard::Continue,
        }
    }

    /// The view a pipe prints again once it heard `frame`: after a report,
    /// and after an account frame of the document followed at the version of
    /// its report, which only an admission sends. A pipe prints the document
    /// alone.
    ///
    /// # Specification
    /// trivial.
    fn reprinted(
        &self,
        frame: &RenderFrame,
    ) -> Option<Rendering>
    {
        let shown = match (frame.scope(), frame.body()) {
            (_, &FrameBody::Frame { .. }) => true,
            (
                &FrameScope::Document(ref document),
                &(FrameBody::Accounts { .. } | FrameBody::AccountPatch { .. }),
            ) => {
                self.latest.as_ref() == Some(&document.uri)
                    && self
                        .reports
                        .get(&document.uri)
                        .is_some_and(|&(ref reported, _)| reported == document)
            },
            (
                _,
                &(FrameBody::Hello { .. }
                | FrameBody::Resync
                | FrameBody::Accounts { .. }
                | FrameBody::AccountPatch { .. }
                | FrameBody::Stack { .. }
                | FrameBody::Activity { .. }
                | FrameBody::Detach),
            ) => false,
        };
        shown.then(|| rendering(&self.followed()))
    }

    /// The frame of the document followed alone, with no activity: the empty
    /// frame before any report.
    ///
    /// # Specification
    /// trivial.
    fn followed(&self) -> Frame
    {
        self.latest
            .as_ref()
            .and_then(|uri| Some((self.reports.get(uri)?, self.accounts.get(uri))))
            .map_or_else(Frame::default, |(&(ref document, ref report), account)| {
                framed(document, report, account)
            })
    }

    /// The panes of the rendering of [`Following::frame`], parted into those of
    /// the document and those of the activity at their end: the pane of the
    /// cores and the pane of the totals.
    ///
    /// # Specification
    /// trivial.
    fn parted<'panes>(
        &self,
        panes: &'panes [Pane],
    ) -> (&'panes [Pane], &'panes [Pane])
    {
        let activity = self.activity.as_ref().map_or(0, |activity| {
            usize::from(!activity.cores.is_empty()).saturating_add(1)
        });
        panes.split_at(panes.len().saturating_sub(activity))
    }

    /// The frame of the document followed and of the pool: what the view
    /// shows, as named fields in the order it shows them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the empty frame before any report and any activity. A report
    ///   gives a frame at the document's version. Its first record holds the
    ///   document's `uri`, its `version`, and the counts of its `diagnostics`
    ///   and its `holes`. A record per account card follows, at the account's
    ///   version: its `declaration`, its `kernel` warrant and its `tier` (both
    ///   absent when the kernel was offered nothing), its `verdict`, and its
    ///   `compile` tier, its counts and its `timing` when the card holds them.
    ///   A record per card follows: its one-based `span` (absent for a card
    ///   placed nowhere), its `code` (absent when the code is not the
    ///   registry's own), one `message` per line of its message, and one
    ///   `chain` per step of its derivation. A record per hole follows: its
    ///   `span`, an absent `code` and its `message`. So a card that comes or
    ///   goes moves no row of the account. Each text is trimmed, and an empty
    ///   line or step is left out. A span is a row and a column, both
    ///   one-based. Rows end where the language server's rows end, and the
    ///   column counts characters. A record per spine of the document's stack
    ///   card follows, at the card's version, the innermost first: its `head`,
    ///   its `type` with the run its slot's parameter writes marked, its `slot`
    ///   as the slot's one-based ordinal over the arity, and the `expected`
    ///   type, each absent when the card holds none. The activity of the pool
    ///   comes last, at the frame's revision: a record per core with its
    ///   `world`, its `core`, its `occupancy`, its task `now`, its `busy` time
    ///   and the `lengths` of its tasks, then the totals record with the count
    ///   of the `cores`, their `occupancy`, their `busy` time and their
    ///   `lengths`. An absent world, an idle core and a window with no ended
    ///   task leave their fields absent.
    /// - provides: the one model that the terminal renders, and that a pipe
    ///   renders without the activity.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report with a placed card, an unplaced card with a
    ///   registry code and a hole builds exact records, and the rendering of
    ///   those records breaks no rule; the empty view builds the empty frame.
    ///   An account of three declarations builds one record each, a stale one
    ///   in the pending hue. The activity of two cores and the totals build one
    ///   record each, after the document's records.
    /// - witness: `follow::tests::a_report_lays_out_its_cards_and_holes`
    /// - witness: `follow::tests::the_view_shows_one_row_per_declaration_of_the_account`
    /// - witness: `follow::tests::the_view_shows_the_activity_of_the_pool`
    /// - witness: `follow::tests::the_view_shows_the_stack_at_the_cursor`
    #[spec(ensures: |ret| ret.records.is_empty() == (self.latest.is_none() && self.activity.is_none()))]
    #[must_use]
    #[inline]
    pub fn frame(&self) -> Frame
    {
        let mut frame = self.followed();
        if let Some(&(ref stacked, ref card)) =
            self.latest.as_ref().and_then(|uri| self.stacks.get(uri))
            && self.reports.contains_key(&stacked.uri)
        {
            frame.records.extend(stack_records(
                card,
                Revision(i64::from(i32::from(stacked.version))),
            ));
        }
        if let Some(ref activity) = self.activity {
            frame
                .records
                .extend(activity_records(activity, frame.revision));
        }
        frame
    }
}

/// The records of the stack pane of `card`, computed for `revision`: one per
/// spine, the innermost first.
///
/// # Specification
/// trivial.
fn stack_records(
    card: &StackCard,
    revision: Revision,
) -> Vec<Record>
{
    let entry = |name: &'static str, datum: Datum| Field {
        name: FieldName::from(name),
        datum,
        revision,
    };
    card.rows
        .iter()
        .map(|row| {
            let ty = match (row.ty.as_ref(), row.filled) {
                (Some(ty), Some(run)) => Datum::Marked {
                    text: ty.clone(),
                    run,
                },
                (Some(ty), None) => Datum::Text(ty.clone()),
                (None, _) => Datum::Absent,
            };
            let slot = row.arity.map_or(Datum::Absent, |arity| Datum::Ratio {
                hits: Count(row.slot.0.saturating_add(1)),
                total: arity,
            });
            Record {
                fields: Vec::from([
                    entry("head", Datum::Text(row.head.clone())),
                    entry("type", ty),
                    entry("slot", slot),
                    entry(
                        "expected",
                        row.expected.clone().map_or(Datum::Absent, Datum::Text),
                    ),
                ]),
            }
        })
        .collect()
}

/// The records of the activity pane of `activity`, computed for `revision`:
/// one per core, then the totals.
///
/// # Specification
/// trivial.
fn activity_records(
    activity: &PoolActivity,
    revision: Revision,
) -> Vec<Record>
{
    let field = |name: &'static str, datum: Datum| Field {
        name: FieldName::from(name),
        datum,
        revision,
    };
    let window = Duration::from_nanos(activity.window.0);
    let load = |load: &Load| {
        [
            field("occupancy", Datum::Samples(load.occupancy.clone())),
            field("busy", Datum::Duration {
                time: Duration::from_nanos(load.busy.0),
                window: Some(window),
            }),
            field(
                "lengths",
                load.lengths
                    .map_or(Datum::Absent, |lengths| Datum::Latency {
                        p50: Duration::from_nanos(lengths.p50.0),
                        p99: Duration::from_nanos(lengths.p99.0),
                        window,
                    }),
            ),
        ]
    };
    let mut records = Vec::with_capacity(activity.cores.len().saturating_add(1));
    for core in &activity.cores {
        let [occupancy, busy, lengths] = load(&core.load);
        records.push(Record {
            fields: Vec::from([
                field("world", core.world.map_or(Datum::Absent, Datum::Count)),
                field("core", Datum::Count(core.core)),
                occupancy,
                field(
                    "now",
                    core.now.map_or(Datum::Absent, |now| {
                        Datum::Text(String::from(<&str>::from(now)))
                    }),
                ),
                busy,
                lengths,
            ]),
        });
    }
    let [occupancy, busy, lengths] = load(&activity.totals);
    records.push(Record {
        fields: Vec::from([
            field(
                "cores",
                Datum::Count(Count(
                    u64::try_from(activity.cores.len()).unwrap_or(u64::MAX),
                )),
            ),
            occupancy,
            busy,
            lengths,
        ]),
    });
    records
}

/// The frame of `report`, the report of `document`, with the records of
/// `account` after its own and before the cards: what [`Following::frame`]
/// answers while `document` is the one followed. A card that comes or goes
/// thus never moves a row of the account.
///
/// # Specification
/// trivial.
fn framed(
    document: &DocId,
    report: &ReportView,
    account: Option<&(DocId, Vec<AccountCard>)>,
) -> Frame
{
    let revision = Revision(i64::from(i32::from(document.version)));
    let field = |name: &'static str, datum: Datum| Field {
        name: FieldName::from(name),
        datum,
        revision,
    };
    let text = |line: &str| Datum::Text(String::from(line.trim()));
    let rows = LineIndex::new(SourceText::from(report.source.as_str()));
    let span = |start: ByteOffset| {
        let row = rows.row_of_byte(start);
        report
            .source
            .get(usize::from(rows.row_bytes(row).start()) .. usize::from(start))
            .map_or(Datum::Absent, |before| {
                Datum::Text(spelled(format_args!(
                    "{}:{}",
                    usize::from(row).saturating_add(1),
                    before.chars().count().saturating_add(1)
                )))
            })
    };
    let count = |count: usize| Datum::Count(Count(u64::try_from(count).unwrap_or(u64::MAX)));
    let holes = report
        .marks
        .iter()
        .filter(|mark| mark.kind == MarkKind::EmptyHole);
    let mut records = Vec::with_capacity(
        report
            .diagnostics
            .len()
            .saturating_add(report.marks.len())
            .saturating_add(account.map_or(0, |&(_, ref cards)| cards.len()))
            .saturating_add(1),
    );
    records.push(Record {
        fields: Vec::from([
            field(
                DOCUMENT,
                Datum::Text(spelled(format_args!("{}", document.uri))),
            ),
            field(
                "version",
                Datum::Text(spelled(format_args!("{}", i32::from(document.version)))),
            ),
            field("diagnostics", count(report.diagnostics.len())),
            field("holes", count(holes.clone().count())),
        ]),
    });
    if let Some(&(ref accounted, ref cards)) = account {
        records.extend(cards.iter().map(|card| Record {
            fields: account_fields(card, Revision(i64::from(i32::from(accounted.version)))),
        }));
    }
    for card in &report.diagnostics {
        let code = if card.code == DiagnosticCode::Other {
            Datum::Absent
        }
        else {
            Datum::Text(spelled(format_args!("{}", card.code)))
        };
        let mut fields = Vec::from([
            field(
                "span",
                card.span
                    .map_or(Datum::Absent, |placed| span(placed.start())),
            ),
            field("code", code),
        ]);
        fields.extend(
            card.message
                .lines()
                .filter(|line| !line.trim().is_empty())
                .map(|line| field("message", text(line))),
        );
        fields.extend(
            card.chain
                .iter()
                .filter(|step| !step.trim().is_empty())
                .map(|step| field("chain", text(step))),
        );
        records.push(Record { fields });
    }
    records.extend(holes.map(|hole| Record {
        fields: Vec::from([
            field("span", span(hole.range.start())),
            field("code", Datum::Absent),
            field("message", text(&hole.message)),
        ]),
    }));
    Frame { revision, records }
}

/// The fields of the record of `card`, computed for `revision`: its
/// declaration, its kernel warrant and tier, its verdict, then the compile
/// tier, the counts and the timing that it holds.
///
/// # Specification
/// trivial.
fn account_fields(
    card: &AccountCard,
    revision: Revision,
) -> Vec<Field>
{
    let entry = |name: &'static str, datum: Datum| Field {
        name: FieldName::from(name),
        datum,
        revision,
    };
    let (kernel, tier) = card
        .kernel
        .as_ref()
        .map_or((Datum::Absent, Datum::Absent), |mark| {
            let tier = mark.title.strip_prefix("kernel ").unwrap_or(&mark.title);
            (
                Datum::Warrant(mark.warrant),
                Datum::Text(String::from(tier)),
            )
        });
    let mut fields = Vec::from([
        entry("declaration", Datum::Text(card.name.clone())),
        entry("kernel", kernel),
        entry("tier", tier),
        entry(
            "verdict",
            Datum::Text(String::from(<&str>::from(card.verdict))),
        ),
    ]);
    if let Some(compile) = card.compile {
        fields.push(entry(
            "compile",
            Datum::Text(String::from(<&str>::from(compile))),
        ));
    }
    if let Some(counts) = card.counts {
        fields.extend(
            [
                ("hits", counts.hits),
                ("misses", counts.misses),
                ("nodes", counts.nodes),
                ("molded", counts.molded),
                ("judged", counts.judged),
                ("crossed", counts.crossed),
                ("obligations", counts.obligations),
                ("recalled", counts.recalled),
                ("expanded", counts.expanded),
                ("kept", counts.kept),
            ]
            .map(|(name, count)| entry(name, Datum::Count(count))),
        );
    }
    if let Some(ref timing) = card.timing {
        fields.push(entry("timing", Datum::Samples(timing.clone())));
    }
    fields
}

/// The text `arguments` spell: each field of a frame owns its text.
///
/// # Specification
/// trivial.
fn spelled(arguments: fmt::Arguments<'_>) -> String
{
    alloc::fmt::format(arguments)
}

/// The side view's rendering of `frame`, a frame [`Following::frame`] builds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: nothing for the empty frame. Otherwise a pane for each run of
///   records whose first fields share one name, in the frame's order. The
///   record that names the document, whose first field is its `uri`, takes a
///   pane of one row, which draws each field as its name beside its datum. Each
///   other run takes a pane under one head per field name that the run uses, in
///   the order the run first uses it, and two heads for a name that holds a
///   latency. Each record takes a row, and a further row while one name holds
///   more fields; each field sits in its name's column. A text sits at the left
///   and a count is a numeral at the right. A warrant is its glyph in its hue,
///   and a ring of samples is its sparkline under the column's scale. A time is
///   a numeral, and a latency is two numerals, its p50 and its p99, in the
///   column's unit: microseconds below one millisecond and milliseconds from
///   it. A field computed for a revision older than the frame's takes the
///   pending hue. Any other datum draws nothing, and the view's frame holds
///   none. A row that draws nothing is left out.
/// - provides: the one rendering that the terminal and a pipe both paint.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the rendering of a report with a placed card, an unplaced
///   card and a hole paints exact lines and breaks no rule of the visual
///   language, and so does the rendering of an account of three declarations
///   and of the activity of two cores; the driver's witness checks each frame a
///   running hub sends for a corpus source.
/// - witness: `follow::tests::a_report_lays_out_its_cards_and_holes`
/// - witness: `follow::tests::the_view_shows_one_row_per_declaration_of_the_account`
/// - witness: `follow::tests::the_view_shows_the_activity_of_the_pool`
#[spec(ensures: |ret| ret.panes.is_empty() == frame.records.is_empty()
    && ret.panes.len() <= frame.records.len())]
#[must_use]
#[inline]
pub fn rendering(frame: &Frame) -> Rendering
{
    let leading = |record: &Record| record.fields.first().map(|field| field.name);
    let mut panes = Vec::new();
    let mut first = Place {
        record: 0,
        field: 0,
    };
    for run in frame
        .records
        .chunk_by(|earlier, later| leading(earlier) == leading(later))
    {
        if run.first().and_then(leading) == Some(FieldName::from(DOCUMENT)) {
            for record in run {
                panes.push(labelled(record, first, frame.revision));
                first.record = first.record.saturating_add(1);
            }
        }
        else {
            panes.push(tabled(run, first, frame.revision));
            first.record = first.record.saturating_add(run.len());
        }
    }
    Rendering { panes }
}

/// The pane of `record`, which has the place `first` in the frame: one row,
/// each field drawn as its name beside its datum.
///
/// # Specification
/// trivial.
fn labelled(
    record: &Record,
    first: Place,
    revision: Revision,
) -> Pane
{
    let mut cells = Vec::with_capacity(record.fields.len().saturating_mul(2));
    for (index, field) in record.fields.iter().enumerate() {
        let place = Place {
            record: first.record,
            field: index,
        };
        cells.push(Cell::label(place, field.name));
        cells.push(drawn(place, field, None, Half::Whole, revision));
    }
    Pane {
        heads: Vec::new(),
        rows: Vec::from([Row { cells }]),
    }
}

/// Which part of its field a column draws: the whole datum, or the p50 or the
/// p99 of a latency.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Half
{
    /// The whole datum.
    Whole,
    /// The median of a latency.
    Median,
    /// The 99th percentile of a latency.
    Tail,
}

/// `time` in nanoseconds, as a count.
///
/// # Specification
/// trivial.
fn nanos(time: Duration) -> Count
{
    Count(u64::try_from(time.as_nanos()).unwrap_or(u64::MAX))
}

/// The pane of `records`, the first of which has the place `first` in the
/// frame: one head per field name, two for a name that holds a latency, and
/// one row per record and per further field of one name, as [`rendering`]
/// states.
///
/// # Specification
/// trivial.
fn tabled(
    records: &[Record],
    first: Place,
    revision: Revision,
) -> Pane
{
    // The names whose fields hold a latency: each takes two columns, the
    // median and the 99th percentile.
    let paired: BTreeSet<FieldName> = records
        .iter()
        .flat_map(|record| &record.fields)
        .filter(|field| matches!(field.datum, Datum::Latency { .. }))
        .map(|field| field.name)
        .collect();
    let parts = |name: &FieldName| -> &'static [Half] {
        if paired.contains(name) {
            &[Half::Median, Half::Tail]
        }
        else {
            &[Half::Whole]
        }
    };
    let mut heads: Vec<Head> = Vec::new();
    let mut halves: Vec<Half> = Vec::new();
    let mut columns_of: BTreeMap<FieldName, usize> = BTreeMap::new();
    // The scale of each column, and what it counts: the largest ceiling,
    // window, sample or time of the column.
    let mut tops: Vec<Option<(Count, SampleUnit)>> = Vec::new();
    for field in records.iter().flat_map(|record| &record.fields) {
        let width = parts(&field.name).len();
        let column = *columns_of.entry(field.name).or_insert_with(|| {
            for &half in parts(&field.name) {
                heads.push(Head {
                    name: field.name,
                    unit: None,
                });
                halves.push(half);
                tops.push(None);
            }
            heads.len().saturating_sub(width)
        });
        let top = match field.datum {
            Datum::Count(_) | Datum::Ratio { .. } => {
                let unit = if matches!(field.datum, Datum::Ratio { .. }) {
                    Unit::Ratio
                }
                else {
                    Unit::Count
                };
                if let Some(head) = heads.get_mut(column) {
                    head.unit = head.unit.or(Some(unit));
                }
                None
            },
            Datum::Samples(ref ring) => Some((
                ring.values()
                    .iter()
                    .copied()
                    .chain(ring.ceiling())
                    .max()
                    .unwrap_or_default(),
                ring.unit(),
            )),
            Datum::Duration { time, window } => Some((
                nanos(window.map_or(time, |window| window.max(time))),
                SampleUnit::Nanoseconds,
            )),
            Datum::Latency { p99, window, .. } => {
                Some((nanos(window.max(p99)), SampleUnit::Nanoseconds))
            },
            Datum::Absent
            | Datum::Text(_)
            | Datum::Marked { .. }
            | Datum::Bytes(_)
            | Datum::Warrant(_)
            | Datum::Comparison { .. } => None,
        };
        if let Some((top, unit)) = top {
            for held in tops.iter_mut().skip(column).take(width) {
                *held = Some(held.map_or((top, unit), |(was, unit)| (was.max(top), unit)));
            }
        }
    }
    // A column of rings or times draws in one unit under one scale: a count,
    // or a time in microseconds below one millisecond and in milliseconds
    // from it. A ceiling or a window fixes the scale of a live column, so a
    // row that moves leaves the cells of the other rows as they were.
    let scales: Vec<Option<(Count, Unit)>> = tops
        .iter()
        .map(|top| {
            top.map(|(top, unit)| {
                let drawn = match unit {
                    SampleUnit::Count => Unit::Count,
                    SampleUnit::Nanoseconds if top < Count(1_000_000) => Unit::Microseconds,
                    SampleUnit::Nanoseconds => Unit::Milliseconds,
                };
                (top, drawn)
            })
        })
        .collect();
    for (head, scale) in heads.iter_mut().zip(&scales) {
        if let Some((_, unit)) = *scale {
            head.unit = head.unit.or(Some(unit));
        }
    }
    // The fields of each column for the record at hand, kept across records.
    let mut columns: Vec<Vec<usize>> = heads.iter().map(|_| Vec::new()).collect();
    let mut rows = Vec::with_capacity(records.len());
    for (offset, record) in records.iter().enumerate() {
        columns.iter_mut().for_each(Vec::clear);
        for (index, field) in record.fields.iter().enumerate() {
            if let Some(&column) = columns_of.get(&field.name) {
                for held in columns
                    .iter_mut()
                    .skip(column)
                    .take(parts(&field.name).len())
                {
                    held.push(index);
                }
            }
        }
        let depth = columns.iter().map(Vec::len).max().unwrap_or_default();
        for line in 0 .. depth {
            let cells: Vec<Cell> = columns
                .iter()
                .zip(&scales)
                .zip(&halves)
                .map(|((column, &scale), &half)| {
                    column
                        .get(line)
                        .and_then(|&index| {
                            let place = Place {
                                record: first.record.saturating_add(offset),
                                field: index,
                            };
                            record
                                .fields
                                .get(index)
                                .map(|field| drawn(place, field, scale, half, revision))
                        })
                        .unwrap_or_else(Cell::blank)
                })
                .collect();
            if cells
                .iter()
                .any(|cell| !cell.text.is_empty() || cell.numeral.is_some() || cell.glyph.is_some())
            {
                rows.push(Row { cells });
            }
        }
    }
    Pane { heads, rows }
}

/// The cell of `field`, the field at `place`, in a frame at `revision`: a
/// text at the left, a count as a numeral, a warrant as its glyph in its hue,
/// a ring as its sparkline under `scale`, the column's largest ceiling or
/// sample and its unit, and a time as a numeral in that unit. A latency draws
/// the part that `half` names, and the second column of a latency draws
/// nothing of another datum. A field older than `revision` takes the pending
/// hue alone; any other datum draws nothing.
///
/// # Specification
/// trivial.
fn drawn(
    place: Place,
    field: &Field,
    scale: Option<(Count, Unit)>,
    half: Half,
    revision: Revision,
) -> Cell
{
    let placed = Cell {
        place: Some(place),
        ..Cell::blank()
    };
    if half == Half::Tail && !matches!(field.datum, Datum::Latency { .. }) {
        return placed;
    }
    let timed = |time: Duration| {
        scale.map(|(_, unit)| Cell::numeral(place, Numeral::of(nanos(time), unit)))
    };
    let mut cell = match field.datum {
        Datum::Text(ref text) => Cell::text(place, text.clone()),
        Datum::Marked { ref text, run } => Cell {
            attributes: Vec::from([Attribute::Underline(run)]),
            ..Cell::text(place, text.clone())
        },
        Datum::Count(count) => Cell::numeral(place, Numeral::from(count)),
        Datum::Ratio { hits, total } => Cell::numeral(place, Numeral {
            text: spelled(format_args!("{}/{}", hits.0, total.0)),
            unit: Unit::Ratio,
        }),
        Datum::Warrant(warrant) => Cell {
            glyph: Some(warrant.glyph()),
            warrant: Some(warrant),
            attributes: Vec::from([Attribute::Hue(warrant.colour())]),
            ..placed
        },
        Datum::Samples(ref ring) => {
            match scale.and_then(|(top, unit)| Sparkline::of(ring, top, unit)) {
                Some(line) => Cell {
                    text: spelled(format_args!("{} {}", line.cells, line.last.text)),
                    sparkline: Some(line),
                    align: Align::Right,
                    ..placed
                },
                None => placed,
            }
        },
        Datum::Duration { time, .. } => timed(time).unwrap_or(placed),
        Datum::Latency { p50, p99, .. } => match half {
            Half::Median => timed(p50).unwrap_or(placed),
            Half::Tail => timed(p99).unwrap_or(placed),
            Half::Whole => placed,
        },
        Datum::Absent | Datum::Bytes(_) | Datum::Comparison { .. } => placed,
    };
    let inked = !cell.text.is_empty() || cell.glyph.is_some();
    if field.revision < revision && inked {
        cell.attributes
            .retain(|attribute| !matches!(*attribute, Attribute::Hue(_)));
        cell.attributes
            .push(Attribute::Hue(Warrant::Pending.colour()));
    }
    cell
}

/// The lines a painter puts down for `panes`: each pane's heads when it has
/// any, then its rows; each cell padded to its column's width, beside the cell
/// whose attributes name its style. A head shows its field's name and its
/// unit, and a head that repeats the head before it, the second column of a
/// latency, shows nothing. A cell shows its glyph and its text.
///
/// # Specification
/// trivial.
pub fn laid(panes: &[Pane]) -> Vec<Vec<Painted<'_>>>
{
    let measured = |text: &str| Span::raw(text).width();
    let joined = |first: &str, second: &str| {
        let parted = !first.is_empty() && !second.is_empty();
        measured(first)
            .saturating_add(usize::from(parted))
            .saturating_add(measured(second))
    };
    let padded = |first: &str, second: &str, width: usize, align: Align| {
        let gap = width.saturating_sub(joined(first, second));
        let mut padded = String::with_capacity(
            first
                .len()
                .saturating_add(second.len())
                .saturating_add(gap)
                .saturating_add(1),
        );
        if align == Align::Right {
            padded.extend(core::iter::repeat_n(' ', gap));
        }
        padded.push_str(first);
        if !first.is_empty() && !second.is_empty() {
            padded.push(' ');
        }
        padded.push_str(second);
        if align == Align::Left {
            padded.extend(core::iter::repeat_n(' ', gap));
        }
        padded
    };
    let head = |heads: &[Head], column: usize| {
        let Some(held) = heads.get(column)
        else {
            return ("", "", Align::Left);
        };
        let repeated = column.checked_sub(1).and_then(|before| heads.get(before)) == Some(held);
        if repeated {
            return ("", "", Align::Left);
        }
        let align = if held.unit.is_some() {
            Align::Right
        }
        else {
            Align::Left
        };
        (
            <&str>::from(held.name),
            held.unit.map_or("", <&str>::from),
            align,
        )
    };
    let mut lines = Vec::new();
    let mut widths: Vec<usize> = Vec::new();
    for pane in panes {
        widths.clear();
        let drawn = (0 .. pane.heads.len())
            .map(|column| {
                let (name, unit, _) = head(&pane.heads, column);
                joined(name, unit)
            })
            .enumerate()
            .chain(pane.rows.iter().flat_map(|row| {
                row.cells
                    .iter()
                    .map(|held| joined(held.glyph.map_or("", <&str>::from), &held.text))
                    .enumerate()
            }));
        for (column, width) in drawn {
            if widths.len() <= column {
                widths.resize(column.saturating_add(1), 0);
            }
            if let Some(widest) = widths.get_mut(column) {
                *widest = (*widest).max(width);
            }
        }
        let width = |column: usize| widths.get(column).copied().unwrap_or_default();
        if !pane.heads.is_empty() {
            lines.push(
                (0 .. pane.heads.len())
                    .map(|column| {
                        let (name, unit, align) = head(&pane.heads, column);
                        (padded(name, unit, width(column), align), None)
                    })
                    .collect(),
            );
        }
        lines.extend(pane.rows.iter().map(|row| {
            row.cells
                .iter()
                .enumerate()
                .map(|(column, held)| {
                    (
                        padded(
                            held.glyph.map_or("", <&str>::from),
                            &held.text,
                            width(column),
                            held.align,
                        ),
                        Some(held),
                    )
                })
                .collect()
        }));
    }
    lines
}

/// The terminal style `cell`'s attributes name: a hue as the theme's colour
/// for its warrant, and the bold and italic weights. An underline marks a run
/// of the text, which [`lines`] draws. The rules refuse every other attribute,
/// so the painter has no paint for it.
///
/// # Specification
/// trivial.
fn painted(cell: &Cell) -> Style
{
    cell.attributes
        .iter()
        .fold(Style::new(), |style, attribute| match *attribute {
            Attribute::Hue(colour) => WARRANTS
                .iter()
                .find(|warrant| warrant.colour() == colour)
                .map_or(style, |&warrant| style.fg(hue_of_warrant(warrant))),
            Attribute::Bold => style.add_modifier(Modifier::BOLD),
            Attribute::Italic => style.add_modifier(Modifier::ITALIC),
            Attribute::Faint
            | Attribute::Opacity
            | Attribute::Background(_)
            | Attribute::Border
            | Attribute::Blink
            | Attribute::Underline(_) => style,
        })
}

/// The text of a painted cell in three pieces: before the run that the cell
/// underlines, the run, and after it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Underlined<'text>
{
    /// The text before the run; the whole text when the cell marks no run.
    pub before: &'text str,
    /// The run that the underline marks; empty when the cell marks none.
    pub run: &'text str,
    /// The text after the run.
    pub after: &'text str,
}

/// The pieces of the padded text of `painted` as a painter draws them: the
/// run that an underline of its cell marks, shifted past the padding before
/// the cell's text, and the text on each side of it.
///
/// # Specification
/// trivial.
pub fn underlined<'text>(painted: &'text Painted<'_>) -> Underlined<'text>
{
    let &(ref text, cell) = painted;
    let run = cell.and_then(|held| {
        held.attributes
            .iter()
            .find_map(|attribute| match *attribute {
                Attribute::Underline(run) => Some(run),
                Attribute::Hue(_)
                | Attribute::Bold
                | Attribute::Italic
                | Attribute::Faint
                | Attribute::Opacity
                | Attribute::Background(_)
                | Attribute::Border
                | Attribute::Blink => None,
            })
    });
    let indent = text
        .len()
        .saturating_sub(text.trim_start_matches(' ').len());
    run.and_then(|run| {
        let start = indent.saturating_add(usize::from(run.start()));
        let end = indent.saturating_add(usize::from(run.end()));
        Some(Underlined {
            before: text.get(.. start)?,
            run: text.get(start .. end)?,
            after: text.get(end ..)?,
        })
    })
    .unwrap_or(Underlined {
        before: text,
        run: "",
        after: "",
    })
}

/// The lines of `rendering` as plain text: the cells of a line parted by one
/// space, with no space at the end.
///
/// # Specification
/// trivial.
fn printed(rendering: &Rendering) -> Vec<String>
{
    laid(&rendering.panes)
        .into_iter()
        .map(|line| {
            let mut text = String::new();
            for (column, (piece, _)) in line.into_iter().enumerate() {
                if column > 0 {
                    text.push(' ');
                }
                text.push_str(&piece);
            }
            text.truncate(text.trim_end().len());
            text
        })
        .collect()
}

/// The lines `gandr view` prints on a pipe for `report`, the report of
/// `document`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the lines that [`follow_plain`] prints after a frame that carries
///   `report` at `document` while it holds no account cards for `document`,
///   without the blank line that parts two reports: the rendering of the
///   report's frame, each line plain text with no space at its end.
/// - provides: the text form of a report for a face with no terminal, such as
///   the agent toolset's display of a result.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the lines of a report with two cards and a hole are the
///   lines that a pipe prints for the same report.
/// - witness: `follow::tests::a_piped_view_prints_each_report`
#[spec(ensures: |ret| ret.iter().all(|line| line.trim_end().len() == line.len()))]
#[must_use]
#[inline]
pub fn report_lines(
    document: &DocId,
    report: &ReportView,
) -> Vec<String>
{
    printed(&rendering(&framed(document, report, None)))
}

/// What the side view's loop acts on next.
#[derive(Debug)]
pub enum Seen
{
    /// A frame the hub sent.
    Frame(RenderFrame),
    /// An input from the terminal.
    Input(Input),
    /// The hub's stream ended, or sent a line that is not a frame.
    Closed,
}

/// Draw `following` onto `screen`: the rendering of its frame, line by line,
/// the activity pane at the foot.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the lines of the activity panes of [`rendering`] of
///   [`Following::frame`] are painted at the foot of the screen, as many as
///   fit, and the first lines of the panes before them that fit above them are
///   painted from the top. Each cell is in the style its attributes name, as a
///   pipe prints it; nothing else is painted.
/// - provides: the side view's one paint.
/// - fails: never.
/// - panics: none.
/// - executable: none — `Frame` exposes its painted buffer only through a
///   mutable borrow, unavailable to a predicate's `Fn` closure. Backend
///   witnesses observe the paint.
///
/// # Adequacy
/// - hypothesis: L3 — a scripted bus paints nothing before a report, then the
///   report's lines exactly as a pipe prints them, observed through backend
///   cells; the activity of two cores sits at the foot under a report.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
/// - witness: `follow::tests::the_view_shows_the_activity_of_the_pool`
#[inline]
pub fn draw_following(
    screen: &mut ratatui::Frame<'_>,
    following: &Following,
)
{
    let drawn = rendering(&following.frame());
    let (document, activity) = following.parted(&drawn.panes);
    let foot = lines(laid(activity));
    let area = screen.area();
    let height = u16::try_from(foot.len())
        .unwrap_or(u16::MAX)
        .min(area.height);
    let [top, bottom] =
        Layout::vertical([Constraint::Min(0), Constraint::Length(height)]).areas(area);
    screen.render_widget(Paragraph::new(lines(laid(document))), top);
    screen.render_widget(Paragraph::new(foot), bottom);
}

/// The terminal lines of `laid`: the cells of a line parted by one space, each
/// in the style its attributes name.
///
/// # Specification
/// trivial.
fn lines(laid: Vec<Vec<Painted<'_>>>) -> Vec<Line<'static>>
{
    laid.into_iter()
        .map(|line| {
            let mut spans = Vec::with_capacity(line.len().saturating_mul(4));
            for (column, drawn) in line.iter().enumerate() {
                if column > 0 {
                    spans.push(Span::raw(" "));
                }
                let style = drawn.1.map_or_else(Style::new, painted);
                let pieces = underlined(drawn);
                for (piece, styled) in [
                    (pieces.before, style),
                    (pieces.run, style.add_modifier(Modifier::UNDERLINED)),
                    (pieces.after, style),
                ] {
                    if !piece.is_empty() {
                        spans.push(Span::styled(String::from(piece), styled));
                    }
                }
            }
            Line::from(spans)
        })
        .collect()
}

/// Run the side view over `terminal`, acting on what `seen` delivers, until
/// the hub closes the bus or the user leaves.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the view is drawn before every wait. A frame goes through
///   [`Following::hear`]; a detach, the end of the hub's stream, a quit, an
///   interrupt or `q` complete the view; a failed input ends it faulted; every
///   other input redraws. A channel with no sender left completes the view.
/// - provides: the side view's event loop, the same on the terminal and under a
///   test's scripted bus.
/// - fails: the backend's error when a frame cannot be drawn.
/// - panics: none.
/// - executable: none — neither the channel nor the backend exposes what was
///   consumed or painted to a predicate.
///
/// # Errors
/// The backend's error when a frame cannot be drawn.
///
/// # Adequacy
/// - hypothesis: L3 — a scripted bus of a greeting, a report and a quit paints
///   the report and completes; a detach completes.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
#[inline]
pub fn drive_following<Screen>(
    terminal: &mut Terminal<Screen>,
    seen: &Receiver<Seen>,
) -> Result<Ended, Screen::Error>
where
    Screen: Backend,
{
    let mut following = Following::default();
    loop {
        let _frame = terminal.draw(|frame| draw_following(frame, &following))?;
        match seen.recv() {
            Ok(Seen::Frame(frame)) => {
                if following.hear(&frame) == Heard::Detached {
                    return Ok(Ended::Completed);
                }
            },
            Ok(
                Seen::Input(Input::Key(Key::Quit | Key::Interrupt | Key::Char('q'))) | Seen::Closed,
            )
            | Err(_) => {
                return Ok(Ended::Completed);
            },
            Ok(Seen::Input(Input::Failed(fault))) => return Ok(Ended::Faulted(fault)),
            Ok(Seen::Input(
                Input::Redraw | Input::Key(Key::Char(_) | Key::Backspace | Key::Enter),
            )) => {},
        }
    }
}

/// Send every frame `reading` carries to `seen`, then [`Seen::Closed`].
///
/// # Specification
/// trivial.
fn frames<Reading>(
    reading: Reading,
    seen: &Sender<Seen>,
) where
    Reading: BufRead,
{
    for line in reading.lines() {
        let Ok(frame) = line.map(|line| serde_json::from_str::<RenderFrame>(&line))
        else {
            break;
        };
        let Ok(frame) = frame
        else {
            break;
        };
        if seen.send(Seen::Frame(frame)).is_err() {
            return;
        }
    }
    drop(seen.send(Seen::Closed));
}

/// Follow the render bus `reading` carries on the process's terminal until the
/// hub closes it or the user leaves, then send the hub a detach on `writing`.
///
/// # Specification
/// - requires: standard input and output are a terminal; `reading` and
///   `writing` are the two ends of a connection whose attach was sent.
/// - ensures: the terminal is put in raw mode on the alternate screen, the view
///   runs as [`drive_following`] states over the bus's frames and the
///   terminal's keys, and the terminal is restored on every ending.
/// - provides: `gandr view` on a terminal.
/// - fails: the terminal's error when it cannot be claimed, drawn on or
///   restored.
/// - panics: none.
/// - executable: none — the effects are the terminal's and a socket's.
///
/// # Errors
/// The terminal's error when it cannot be claimed, drawn on or restored.
///
/// # Adequacy
/// - hypothesis: L3 — the loop it runs is witnessed under a scripted bus. On a
///   pseudo-terminal on Linux, a bus the hub has already closed completes the
///   view, sends one detach line, and leaves the terminal's settings as they
///   were.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
/// - witness: `tests::terminal::the_side_view_claims_and_restores_a_terminal`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the frame reader and the keyboard reader each block on their input for the view's life"
    )
)]
#[inline]
pub fn follow<Reading, Writing>(
    reading: Reading,
    writing: &mut Writing,
) -> io::Result<Ended>
where
    Reading: BufRead + Send + 'static,
    Writing: Write,
{
    let (seen, inbox) = channel();
    let keys = seen.clone();
    drop(thread::spawn(move || frames(reading, &seen)));
    let ended = match ratatui::try_init() {
        Ok(mut terminal) => {
            // The keyboard is read on its own thread, started once the
            // terminal is raw so crossterm's reader sees each key as it is
            // pressed; frames paint while no key is. The thread ends with the
            // process.
            drop(thread::spawn(move || {
                let mut keyboard = Keyboard;
                loop {
                    let input = keyboard.next();
                    let failed = matches!(input, Input::Failed(_));
                    if keys.send(Seen::Input(input)).is_err() || failed {
                        break;
                    }
                }
            }));
            drive_following(&mut terminal, &inbox)
        },
        Err(error) => Err(error),
    };
    let restored = ratatui::try_restore();
    drop(detach(writing));
    match (ended, restored) {
        (Ok(ended), Ok(())) => Ok(ended),
        (Err(error), _) | (Ok(_), Err(error)) => Err(error),
    }
}

/// Send the hub a detach on `writing`.
///
/// # Specification
/// trivial.
fn detach<Writing>(writing: &mut Writing) -> io::Result<()>
where
    Writing: Write,
{
    let mut line = serde_json::to_string(&RenderFrame::detach()).map_err(io::Error::other)?;
    line.push('\n');
    writing.write_all(line.as_bytes())?;
    writing.flush()
}

/// Follow the render bus `reading` carries as plain text, printing the view
/// to `output` after each frame that changes what it shows.
///
/// # Specification
/// - requires: `reading` carries the bus's frames, one per line.
/// - ensures: each frame is heard as [`Following::hear`] states. After a
///   report, and after an account frame of the followed document at the version
///   of its report, the lines of [`rendering`] of [`Following::frame`] are
///   written and flushed at once, each cell padded to its column and parted
///   from the next by one space. Greetings, resyncs and the account frames that
///   come before their report write nothing. The view completes at a detach or
///   the end of the stream, and ends faulted when a line is not a frame or
///   cannot be read.
/// - provides: `gandr view` when standard output is not a terminal.
/// - fails: the writer's error.
/// - panics: none.
/// - executable: none — `output` is written, not read back.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — two reports for one document print two blocks of lines,
///   each its version's, and a detach ends the view; the driver's own witness
///   runs it piped through a running hub.
/// - witness: `follow::tests::a_piped_view_prints_each_report`
#[inline]
pub fn follow_plain<Reading, Output>(
    reading: Reading,
    output: &mut Output,
) -> io::Result<Ended>
where
    Reading: BufRead,
    Output: Write,
{
    let mut following = Following::default();
    for line in reading.lines() {
        let line = match line {
            Ok(line) => line,
            Err(error) => return Ok(Ended::Faulted(Fault::Input(error))),
        };
        let frame = match serde_json::from_str::<RenderFrame>(&line) {
            Ok(frame) => frame,
            Err(error) => {
                return Ok(Ended::Faulted(Fault::Input(io::Error::new(
                    io::ErrorKind::InvalidData,
                    error,
                ))));
            },
        };
        if following.hear(&frame) == Heard::Detached {
            break;
        }
        if let Some(view) = following.reprinted(&frame) {
            for shown in printed(&view) {
                writeln!(output, "{shown}")?;
            }
            writeln!(output)?;
            output.flush()?;
        }
    }
    Ok(Ended::Completed)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;
    use std::io;
    use std::sync::mpsc::channel;

    use gandr_surface_render_remote::AccountCard;
    use gandr_surface_render_remote::AccountEdit;
    use gandr_surface_render_remote::AccountKey;
    use gandr_surface_render_remote::Attribute;
    use gandr_surface_render_remote::Breach;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::CheckerVerdict;
    use gandr_surface_render_remote::CoreActivity;
    use gandr_surface_render_remote::Count;
    use gandr_surface_render_remote::Datum;
    use gandr_surface_render_remote::DiagCard;
    use gandr_surface_render_remote::DiagnosticCode;
    use gandr_surface_render_remote::DocId;
    use gandr_surface_render_remote::DocVersion;
    use gandr_surface_render_remote::DocumentUri;
    use gandr_surface_render_remote::KernelMark;
    use gandr_surface_render_remote::Lengths;
    use gandr_surface_render_remote::Load;
    use gandr_surface_render_remote::MarkKind;
    use gandr_surface_render_remote::MarkSpan;
    use gandr_surface_render_remote::PoolActivity;
    use gandr_surface_render_remote::RenderFrame;
    use gandr_surface_render_remote::ReportView;
    use gandr_surface_render_remote::SampleUnit;
    use gandr_surface_render_remote::Samples;
    use gandr_surface_render_remote::Shown;
    use gandr_surface_render_remote::SpineRow;
    use gandr_surface_render_remote::StackCard;
    use gandr_surface_render_remote::TaskKind;
    use gandr_surface_render_remote::Warrant;
    use gandr_surface_render_remote::conform;
    use gandr_surface_repl::Ended;
    use gandr_surface_repl::Fault;
    use ratatui::Terminal;
    use ratatui::backend::TestBackend;

    use super::Following;
    use super::Heard;
    use super::Seen;
    use super::detach;
    use super::drive_following;
    use super::follow_plain;
    use super::frames;
    use super::printed;
    use super::rendering;
    use crate::app::Key;
    use crate::run::Input;

    /// The lines the view prints for `following`.
    ///
    /// # Specification
    /// trivial.
    fn lines(following: &Following) -> Vec<String>
    {
        printed(&rendering(&following.frame()))
    }

    /// The rules that the rendering of `following`'s frame breaks, after the
    /// frame and the rendering of `before`.
    ///
    /// # Specification
    /// trivial.
    fn breaches(
        following: &Following,
        before: &Following,
    ) -> Vec<Breach>
    {
        let (frame, earlier) = (following.frame(), before.frame());
        conform(&Shown {
            frame: &frame,
            rendering: &rendering(&frame),
            before: Some((&earlier, &rendering(&earlier))),
        })
    }

    /// The document `name` at `version`.
    ///
    /// # Specification
    /// trivial.
    fn document(
        name: &DocumentUri,
        version: DocVersion,
    ) -> DocId
    {
        DocId {
            uri: name.clone(),
            version,
        }
    }

    /// The byte range `[start, end)`.
    ///
    /// # Specification
    /// trivial.
    fn bytes(
        start: ByteOffset,
        end: ByteOffset,
    ) -> ByteRange
    {
        ByteRange::new(start, end).expect("an ordered range")
    }

    /// A report over `def f : Integer ;\ndef f = "one" ;\ndef g = ?gap ;\n`:
    /// a refusal at the literal with one derivation step, an unplaced fault
    /// under a registry code, and a hole.
    ///
    /// # Specification
    /// trivial.
    fn refused() -> ReportView
    {
        let source = "def f : Integer ;\ndef f = \"one\" ;\ndef g = ?gap ;\n";
        let literal = source.find("\"one\"").expect("the literal");
        let hole = source.find("?gap").expect("the hole");
        ReportView {
            source: String::from(source),
            diagnostics: Vec::from([
                DiagCard {
                    code: DiagnosticCode::Other,
                    message: String::from("[type-mismatch] mismatched types\nexpected `Integer`"),
                    span: Some(bytes(
                        ByteOffset::from(literal),
                        ByteOffset::from(literal.saturating_add(5_usize)),
                    )),
                    expr: None,
                    elaboration: None,
                    chain: Vec::from([String::from("the type it is checked against")]),
                },
                DiagCard {
                    code: DiagnosticCode::ParseRepair,
                    message: String::from("parse repaired"),
                    span: None,
                    expr: None,
                    elaboration: None,
                    chain: Vec::new(),
                },
            ]),
            marks: Vec::from([MarkSpan {
                range: bytes(
                    ByteOffset::from(hole),
                    ByteOffset::from(hole.saturating_add(4_usize)),
                ),
                kind: MarkKind::EmptyHole,
                message: String::from("goal ?gap : Integer"),
            }]),
            ..ReportView::default()
        }
    }

    #[test]
    fn the_view_follows_the_document_checked_last()
    {
        let (a, b) = (
            DocumentUri::from(String::from("file:///a.gandr")),
            DocumentUri::from(String::from("file:///b.gandr")),
        );
        let mut following = Following::default();
        let heading = |following: &Following| lines(following).first().cloned();
        assert_eq!(
            following.hear(&RenderFrame::hello(Vec::from([document(
                &a,
                DocVersion::from(1_i32)
            )]))),
            Heard::Continue
        );
        assert_eq!(
            heading(&following),
            None,
            "a greeting reports nothing, and an empty frame draws nothing"
        );
        for (uri, version) in [(&a, 1_i32), (&b, 4_i32)] {
            let before = following.clone();
            assert_eq!(
                following.hear(&RenderFrame::frame(
                    document(uri, DocVersion::from(version)),
                    ReportView::default()
                )),
                Heard::Continue
            );
            assert_eq!(breaches(&following, &before), []);
        }
        assert_eq!(
            heading(&following).as_deref(),
            Some("uri file:///b.gandr version 4 diagnostics 0 holes 0"),
            "the second report is followed"
        );
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&a, DocVersion::from(2_i32)),
                ReportView::default(),
            )),
            Heard::Continue
        );
        assert_eq!(
            heading(&following).as_deref(),
            Some("uri file:///a.gandr version 2 diagnostics 0 holes 0"),
            "a newer report of the first document follows it again"
        );
        assert_eq!(following.hear(&RenderFrame::detach()), Heard::Detached);
    }

    #[test]
    fn a_report_lays_out_its_cards_and_holes()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let mut following = Following::default();
        let before = following.clone();
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                refused(),
            )),
            Heard::Continue
        );
        assert_eq!(lines(&following), [
            "uri file:///a.gandr version 3 diagnostics 2 holes 1",
            "span code  message                          chain",
            "2:9        [type-mismatch] mismatched types the type it is checked against",
            "           expected `Integer`",
            "     W0012 parse repaired",
            "3:9        goal ?gap : Integer",
        ]);
        assert_eq!(
            breaches(&following, &before),
            [],
            "the layout keeps every rule of the visual language"
        );
    }

    #[test]
    fn a_hole_inside_a_character_is_placed_nowhere()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let mut following = Following::default();
        let source = "def é = ?gap ;\n";
        let inside = source
            .find('é')
            .expect("the letter")
            .saturating_add(1_usize);
        let report = ReportView {
            source: String::from(source),
            marks: Vec::from([MarkSpan {
                range: bytes(
                    ByteOffset::from(inside),
                    ByteOffset::from(inside.saturating_add(4_usize)),
                ),
                kind: MarkKind::EmptyHole,
                message: String::from("goal ?gap : Integer"),
            }]),
            ..ReportView::default()
        };
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&uri, DocVersion::from(1_i32)),
                report,
            )),
            Heard::Continue
        );
        assert_eq!(
            following
                .frame()
                .records
                .get(1)
                .and_then(|hole| hole.fields.first())
                .map(|span| &span.datum),
            Some(&Datum::Absent)
        );
        assert_eq!(
            lines(&following).last().map(String::as_str),
            Some("          goal ?gap : Integer")
        );
    }

    /// A declaration of a test account: its key, its name, and its kernel
    /// tier as a warrant and a title.
    #[derive(Clone, Copy)]
    struct Declared
    {
        /// The card's key.
        key: &'static str,
        /// The declaration's name.
        name: &'static str,
        /// The kernel tier, if the account holds one.
        kernel: Option<(Warrant, &'static str)>,
    }

    impl Declared
    {
        /// The declaration's card, checked, with `timing` as its ring.
        ///
        /// # Specification
        /// trivial.
        fn card(
            self,
            timing: Option<Samples>,
        ) -> AccountCard
        {
            AccountCard {
                key: AccountKey::from(String::from(self.key)),
                name: String::from(self.name),
                verdict: CheckerVerdict::Checked,
                kernel: self.kernel.map(|(warrant, title)| KernelMark {
                    warrant,
                    title: String::from(title),
                }),
                compile: None,
                counts: None,
                timing,
            }
        }
    }

    #[test]
    fn the_view_shows_one_row_per_declaration_of_the_account()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let at = |version: i32| document(&uri, DocVersion::from(version));
        let ring = Samples::new(
            SampleUnit::Nanoseconds,
            Vec::from([Count(5_000), Count(10_000), Count(20_000)]),
        )
        .expect("a ring of three samples");
        let mut following = Following::default();
        let snapshot = RenderFrame::accounts(
            at(1_i32),
            Vec::from([
                Declared {
                    key: "a",
                    name: "one",
                    kernel: Some((Warrant::Pending, "kernel pending")),
                }
                .card(None),
                Declared {
                    key: "b",
                    name: "two",
                    kernel: None,
                }
                .card(None),
            ]),
        );
        assert_eq!(following.hear(&snapshot), Heard::Continue);
        assert!(
            following.frame().records.is_empty(),
            "an account follows no document before its report"
        );
        let _heard = following.hear(&RenderFrame::frame(at(1_i32), ReportView::default()));
        let before = following.clone();
        let patch = RenderFrame::account_patch(
            at(1_i32),
            Vec::from([
                AccountEdit::Put {
                    at: 0,
                    card: Declared {
                        key: "a",
                        name: "one",
                        kernel: Some((Warrant::Replayed, "kernel replayed")),
                    }
                    .card(Some(ring.clone())),
                },
                AccountEdit::Put {
                    at: 2,
                    card: Declared {
                        key: "c",
                        name: "three",
                        kernel: Some((Warrant::Withheld, "kernel withheld: behind one")),
                    }
                    .card(Some(ring)),
                },
            ]),
        );
        assert_eq!(following.hear(&patch), Heard::Continue);
        let line = "▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▃▅█ 20.0";
        assert_eq!(lines(&following), [
            String::from("uri file:///a.gandr version 1 diagnostics 0 holes 0"),
            String::from(
                "declaration kernel tier                 verdict                             timing µs"
            ),
            format!("one         ✓✓     replayed             checked {line}"),
            String::from("two                                     checked"),
            format!("three       ○      withheld: behind one checked {line}"),
        ]);
        assert_eq!(
            breaches(&following, &before),
            [],
            "the account keeps every rule of the visual language"
        );
        let settled = following.clone();
        let _heard = following.hear(&RenderFrame::frame(at(2_i32), ReportView::default()));
        let inked = |following: &Following| -> Vec<Vec<Attribute>> {
            rendering(&following.frame())
                .panes
                .get(1)
                .into_iter()
                .flat_map(|pane| pane.rows.iter().flat_map(|row| &row.cells))
                .filter(|cell| !cell.text.is_empty() || cell.glyph.is_some())
                .map(|cell| cell.attributes.clone())
                .collect()
        };
        assert_eq!(
            inked(&following),
            inked(&settled),
            "a later report leaves the account current, as the bus sends its change first"
        );
        let current = following.clone();
        let cards = following
            .accounts
            .get(&uri)
            .map(|&(_, ref cards)| cards.clone())
            .unwrap_or_default();
        let _heard = following.hear(&RenderFrame::accounts(at(1_i32), cards));
        let pending = Attribute::Hue(Warrant::Pending.colour());
        assert!(
            inked(&following)
                .iter()
                .all(|attributes| *attributes == [pending]),
            "an account older than the report shows in the pending hue: {:?}",
            inked(&following)
        );
        assert_eq!(breaches(&following, &current), []);
    }

    #[test]
    fn the_view_shows_the_stack_at_the_cursor()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let at = |version: i32| document(&uri, DocVersion::from(version));
        let run = |start: usize, end: usize| {
            ByteRange::new(ByteOffset::from(start), ByteOffset::from(end)).expect("an ordered run")
        };
        let typed = String::from("(a : Integer, b : Integer) -> -F Integer");
        let card = StackCard {
            offset: ByteOffset::from(40_usize),
            rows: Vec::from([
                SpineRow {
                    head: String::from("g"),
                    ty: Some(typed.clone()),
                    filled: Some(run(1, 12)),
                    slot: Count(0),
                    arity: Some(Count(2)),
                    expected: Some(String::from("Integer")),
                },
                SpineRow {
                    head: String::from("f"),
                    ty: Some(typed.clone()),
                    filled: Some(run(14, 25)),
                    slot: Count(1),
                    arity: Some(Count(2)),
                    expected: None,
                },
                SpineRow {
                    head: String::from("k"),
                    ty: Some(String::from("Integer -> Integer")),
                    filled: None,
                    slot: Count(0),
                    arity: None,
                    expected: None,
                },
            ]),
        };
        let mut following = Following::default();
        assert_eq!(
            following.hear(&RenderFrame::stack(at(1_i32), card.clone())),
            Heard::Continue
        );
        assert!(
            following.frame().records.is_empty(),
            "a card follows no document before its report"
        );
        let _heard = following.hear(&RenderFrame::frame(at(1_i32), ReportView::default()));
        let before = following.clone();
        let _heard = following.hear(&RenderFrame::stack(at(1_i32), card));
        let row = |head: &str, ty: &str, slot: &str, expected: &str| {
            String::from(format!("{head:<4} {ty:<40} {slot:>4} {expected}").trim_end())
        };
        assert_eq!(lines(&following), [
            String::from("uri file:///a.gandr version 1 diagnostics 0 holes 0"),
            row("head", "type", "slot", "expected"),
            row("g", &typed, "1/2", "Integer"),
            row("f", &typed, "2/2", ""),
            row("k", "Integer -> Integer", "", ""),
        ]);
        let marks = |following: &Following| -> Vec<Vec<Attribute>> {
            rendering(&following.frame())
                .panes
                .get(1)
                .into_iter()
                .flat_map(|pane| &pane.rows)
                .filter_map(|row| row.cells.get(1))
                .map(|cell| cell.attributes.clone())
                .collect()
        };
        assert_eq!(
            marks(&following),
            [
                Vec::from([Attribute::Underline(run(1, 12))]),
                Vec::from([Attribute::Underline(run(14, 25))]),
                Vec::new(),
            ],
            "each type underlines the parameter its slot fills"
        );
        assert_eq!(
            breaches(&following, &before),
            [],
            "the stack pane keeps every rule of the visual language"
        );
        let current = following.clone();
        let _heard = following.hear(&RenderFrame::frame(at(2_i32), ReportView::default()));
        let pending = Attribute::Hue(Warrant::Pending.colour());
        assert!(
            marks(&following)
                .iter()
                .all(|attributes| attributes.last() == Some(&pending)),
            "a card older than the report shows in the pending hue: {:?}",
            marks(&following)
        );
        assert_eq!(breaches(&following, &current), []);
    }

    #[test]
    fn the_view_shows_the_activity_of_the_pool()
    {
        // A ring of the hub's pane: its last two cells after 30 idle ones,
        // under the ceiling of one tick for each core it sums.
        let ring = |last: u64, cores: u64| {
            let mut values = [Count(0); 32];
            if let Some(newest) = values.last_mut() {
                *newest = Count(last);
            }
            Samples::bounded(
                SampleUnit::Nanoseconds,
                values,
                Count(16_666_667_u64.saturating_mul(cores)),
            )
        };
        let lengths = Lengths {
            p50: Count(200_000),
            p99: Count(400_000),
        };
        let busy = |last: u64, lengths: Option<Lengths>| Load {
            occupancy: ring(last, 1),
            busy: Count(last),
            lengths,
        };
        let activity = PoolActivity {
            window: Count(2_000_000_000),
            cores: Vec::from([
                CoreActivity {
                    world: Some(Count(0)),
                    core: Count(0),
                    now: Some(TaskKind::Fork),
                    load: busy(600_000, Some(lengths)),
                },
                CoreActivity {
                    world: None,
                    core: Count(1),
                    now: None,
                    load: busy(0, None),
                },
            ]),
            totals: Load {
                occupancy: ring(600_000, 2),
                busy: Count(600_000),
                lengths: Some(lengths),
            },
        };
        let mut following = Following::default();
        let idle = following.clone();
        assert_eq!(
            following.hear(&RenderFrame::activity(activity.clone())),
            Heard::Continue
        );
        let low = "▁".repeat(32);
        let pane = [
            format!("world core {:>38} now  busy ms lengths ms", "occupancy ms"),
            format!("    0    0 {low} 0.600 fork   0.600      0.200 0.400"),
            format!("         1     {low} 0            0"),
            format!("cores {:>38} busy ms lengths ms", "occupancy ms"),
            format!("    2 {low} 0.600   0.600      0.200 0.400"),
        ];
        assert_eq!(lines(&following), pane, "the pane alone, before any report");
        assert_eq!(breaches(&following, &idle), [], "the pane keeps every rule");
        let started = following.clone();
        let mut moved = activity.clone();
        if let Some(second) = moved.cores.get_mut(1) {
            *second = CoreActivity {
                world: Some(Count(0)),
                core: Count(1),
                now: Some(TaskKind::Fork),
                load: busy(16_666_667, None),
            };
        }
        moved.totals = Load {
            occupancy: ring(17_266_667, 2),
            busy: Count(17_266_667),
            lengths: Some(lengths),
        };
        let _heard = following.hear(&RenderFrame::activity(moved));
        assert_eq!(
            breaches(&following, &started),
            [],
            "a core that fills its tick leaves the scale and the units of the other rows as they were"
        );
        let _heard = following.hear(&RenderFrame::activity(activity.clone()));
        let before = following.clone();
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let report = RenderFrame::frame(
            document(&uri, DocVersion::from(1_i32)),
            ReportView::default(),
        );
        let _heard = following.hear(&report);
        let header = String::from("uri file:///a.gandr version 1 diagnostics 0 holes 0");
        assert_eq!(
            lines(&following),
            core::iter::once(header.clone())
                .chain(pane.iter().cloned())
                .collect::<Vec<_>>(),
            "the pane follows the document"
        );
        assert_eq!(
            breaches(&following, &before),
            [],
            "the report leaves the pane in place"
        );
        let (seen, inbox) = channel();
        for frame in [report.clone(), RenderFrame::activity(activity.clone())] {
            seen.send(Seen::Frame(frame)).expect("the loop listens");
        }
        seen.send(Seen::Input(Input::Key(Key::Char('q'))))
            .expect("the loop listens");
        let mut terminal = Terminal::new(TestBackend::new(80_u16, 8_u16)).expect("a test backend");
        assert!(matches!(
            drive_following(&mut terminal, &inbox),
            Ok(Ended::Completed)
        ));
        let buffer = terminal.backend().buffer();
        let screen: Vec<String> = (buffer.area.top() .. buffer.area.bottom())
            .map(|y| {
                let mut line: String = (buffer.area.left() .. buffer.area.right())
                    .map(|x| buffer[(x, y)].symbol())
                    .collect();
                line.truncate(line.trim_end().len());
                line
            })
            .collect();
        assert_eq!(
            screen,
            [header.clone(), String::new(), String::new()]
                .into_iter()
                .chain(pane.iter().cloned())
                .collect::<Vec<_>>(),
            "the report sits at the top and the pane at the foot"
        );
        let mut bus = String::new();
        for frame in [RenderFrame::activity(activity), report] {
            bus.push_str(&serde_json::to_string(&frame).expect("a frame encodes"));
            bus.push('\n');
        }
        let mut output = Vec::new();
        assert!(matches!(
            follow_plain(bus.as_bytes(), &mut output),
            Ok(Ended::Completed)
        ));
        assert_eq!(
            String::from_utf8(output).expect("the view prints text"),
            format!("{header}\n\n"),
            "a pipe prints the document alone"
        );
    }

    #[test]
    fn the_view_paints_what_the_bus_sends()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let (seen, inbox) = channel();
        for event in [
            Seen::Frame(RenderFrame::hello(Vec::new())),
            Seen::Frame(RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                refused(),
            )),
            Seen::Input(Input::Redraw),
            Seen::Input(Input::Key(Key::Char('x'))),
            Seen::Input(Input::Key(Key::Char('q'))),
            Seen::Frame(RenderFrame::detach()),
        ] {
            seen.send(event).expect("the loop listens");
        }
        let mut terminal = Terminal::new(TestBackend::new(64_u16, 10_u16)).expect("a test backend");
        assert!(matches!(
            drive_following(&mut terminal, &inbox),
            Ok(Ended::Completed)
        ));
        let buffer = terminal.backend().buffer();
        let screen: Vec<String> = (buffer.area.top() .. buffer.area.bottom())
            .map(|y| {
                (buffer.area.left() .. buffer.area.right())
                    .map(|x| buffer[(x, y)].symbol())
                    .collect()
            })
            .collect();
        let piped = lines(&{
            let mut following = Following::default();
            let _heard = following.hear(&RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                refused(),
            ));
            following
        });
        assert_eq!(
            screen
                .iter()
                .map(|line| String::from(line.trim_end()))
                .collect::<Vec<_>>(),
            piped
                .iter()
                .map(|line| {
                    let mut fitted: String = line.chars().take(64).collect();
                    fitted.truncate(fitted.trim_end().len());
                    fitted
                })
                .chain(core::iter::repeat_n(
                    String::new(),
                    10_usize.saturating_sub(piped.len())
                ))
                .collect::<Vec<_>>(),
            "the terminal paints what a pipe prints, and nothing else"
        );
        assert!(
            inbox
                .try_recv()
                .is_ok_and(|event| matches!(event, Seen::Frame(_))),
            "the quit ends the loop before the detach is read"
        );
    }

    #[test]
    fn a_piped_view_prints_each_report()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let mut bus = String::new();
        let accounted = |version: i32, settled: bool| {
            let warrant = if settled {
                (Warrant::Replayed, "kernel replayed")
            }
            else {
                (Warrant::Pending, "kernel pending")
            };
            RenderFrame::account_patch(
                document(&uri, DocVersion::from(version)),
                Vec::from([AccountEdit::Put {
                    at: 0,
                    card: Declared {
                        key: "a",
                        name: "f",
                        kernel: Some(warrant),
                    }
                    .card(None),
                }]),
            )
        };
        for frame in [
            RenderFrame::hello(Vec::from([document(&uri, DocVersion::from(1_i32))])),
            RenderFrame::accounts(document(&uri, DocVersion::from(1_i32)), Vec::new()),
            RenderFrame::frame(document(&uri, DocVersion::from(1_i32)), refused()),
            accounted(1_i32, true),
            accounted(2_i32, false),
            RenderFrame::frame(
                document(&uri, DocVersion::from(2_i32)),
                ReportView::default(),
            ),
            RenderFrame::detach(),
            RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                ReportView::default(),
            ),
        ] {
            bus.push_str(&serde_json::to_string(&frame).expect("a frame encodes"));
            bus.push('\n');
        }
        let mut output = Vec::new();
        assert!(matches!(
            follow_plain(bus.as_bytes(), &mut output),
            Ok(Ended::Completed)
        ));
        let printed = String::from_utf8(output).expect("the lines are text");
        assert_eq!(
            printed
                .split("\n\n")
                .map(|report| report.lines().next().unwrap_or_default())
                .collect::<Vec<_>>(),
            [
                "uri file:///a.gandr version 1 diagnostics 2 holes 1",
                "uri file:///a.gandr version 1 diagnostics 2 holes 1",
                "uri file:///a.gandr version 2 diagnostics 0 holes 0",
                ""
            ],
            "each report prints once, an admission's patch prints its report again, a patch \
             before its report prints nothing, and nothing prints after the detach"
        );
        let report = super::report_lines(&document(&uri, DocVersion::from(1_i32)), &refused());
        assert_eq!(
            printed
                .split("\n\n")
                .next()
                .map(|block| block.lines().map(String::from).collect::<Vec<_>>()),
            Some(report),
            "the lines of a report are the lines a pipe prints for it"
        );
        let mut garbled = Vec::new();
        assert!(matches!(
            follow_plain(&b"not a frame\n"[..], &mut garbled),
            Ok(Ended::Faulted(_))
        ));
    }

    #[test]
    fn a_detach_or_a_failed_input_ends_the_view()
    {
        let mut terminal = Terminal::new(TestBackend::new(64_u16, 10_u16)).expect("a test backend");
        let (seen, inbox) = channel();
        seen.send(Seen::Frame(RenderFrame::detach()))
            .expect("the loop listens");
        assert!(matches!(
            drive_following(&mut terminal, &inbox),
            Ok(Ended::Completed)
        ));
        let (seen, inbox) = channel();
        seen.send(Seen::Input(Input::Failed(Fault::Input(io::Error::other(
            "the keyboard is gone",
        )))))
        .expect("the loop listens");
        assert!(matches!(
            drive_following(&mut terminal, &inbox),
            Ok(Ended::Faulted(Fault::Input(ref error))) if error.to_string() == "the keyboard is gone"
        ));
    }

    #[test]
    fn the_bus_reader_forwards_frames_until_a_line_is_not_one()
    {
        let detached = serde_json::to_string(&RenderFrame::detach()).expect("a frame encodes");
        for bad in [&b"not a frame"[..], &b"\xff"[..]] {
            let mut bus = Vec::from(detached.as_bytes());
            bus.push(b'\n');
            bus.extend_from_slice(bad);
            bus.push(b'\n');
            bus.extend_from_slice(detached.as_bytes());
            bus.push(b'\n');
            let (seen, inbox) = channel();
            frames(bus.as_slice(), &seen);
            let heard: Vec<Seen> = inbox.try_iter().collect();
            assert!(
                matches!(heard.as_slice(), [Seen::Frame(_), Seen::Closed]),
                "{heard:?}"
            );
        }
    }

    #[test]
    fn the_view_leaves_the_hub_with_one_detach_line()
    {
        let mut written = Vec::new();
        detach(&mut written).expect("a vector takes the line");
        let line = String::from_utf8(written).expect("the line is text");
        let frame: RenderFrame = serde_json::from_str(line.strip_suffix('\n').expect("one line"))
            .expect("the line is a frame");
        assert_eq!(Following::default().hear(&frame), Heard::Detached);
    }

    #[test]
    fn a_piped_view_faults_on_a_line_that_is_not_text()
    {
        let mut output = Vec::new();
        assert!(matches!(
            follow_plain(&b"\xff\n"[..], &mut output),
            Ok(Ended::Faulted(Fault::Input(ref error))) if error.kind() == io::ErrorKind::InvalidData
        ));
        assert!(output.is_empty());
    }
}
