use alloc::string::String;
use alloc::vec::Vec;
use core::time::Duration;

use super::At;
use super::Attribute;
use super::BLOCKS;
use super::Cell;
use super::Colour;
use super::Count;
use super::Datum;
use super::Field;
use super::FieldName;
use super::Frame;
use super::Head;
use super::Numeral;
use super::Pane;
use super::Place;
use super::Record;
use super::Rendering;
use super::Revision;
use super::Row;
use super::SAMPLES;
use super::SampleUnit;
use super::Samples;
use super::Shown;
use super::Sparkline;
use super::TooManySamples;
use super::Unit;
use super::WARRANTS;
use super::Warrant;
use super::conform;
use super::patterned;
use crate::present::ByteOffset;
use crate::present::ByteRange;

/// The revision of the example frames.
const NOW: Revision = Revision(2_i64);

/// The field named `name` holding `datum`, computed for `revision`.
///
/// # Specification
/// trivial.
fn field(
    name: FieldName,
    datum: Datum,
    revision: Revision,
) -> Field
{
    Field {
        name,
        datum,
        revision,
    }
}

/// The numeral `$text` in `$unit`.
macro_rules! numeral {
    ($text:expr, $unit:expr) => {
        Numeral {
            text: String::from($text),
            unit: $unit,
        }
    };
}

/// The cell at `at` of `rendering`.
///
/// # Specification
/// trivial.
fn cell(
    rendering: &mut Rendering,
    at: At,
) -> &mut Cell
{
    rendering
        .panes
        .get_mut(at.pane)
        .and_then(|pane| pane.rows.get_mut(at.row))
        .and_then(|row| row.cells.get_mut(at.cell))
        .expect("the example holds the cell")
}

/// A frame of two declarations, each with a warrant, a stale or fresh count,
/// a latency, a ratio, samples, a note and a comparison; the second's note
/// is `note`. Then the rendering that keeps the language: the first name
/// labelled beside its mark, and a pane of one row per declaration under the
/// column heads.
///
/// # Specification
/// trivial.
fn example(note: Datum) -> (Frame, Rendering)
{
    let samples = Samples::new(SampleUnit::Count, (0_u64 .. 32_u64).map(Count).collect())
        .expect("a ring of 32 samples");
    let blocks: String = BLOCKS.iter().cycle().take(32).collect();
    let mut frame = Frame {
        revision: NOW,
        records: Vec::new(),
    };
    let mut rendering = Rendering {
        panes: Vec::from([Pane::default(), Pane {
            heads: Vec::from([
                Head {
                    name: FieldName::from("name"),
                    unit: None,
                },
                Head {
                    name: FieldName::from("warrant"),
                    unit: None,
                },
                Head {
                    name: FieldName::from("judgements"),
                    unit: Some(Unit::Count),
                },
                Head {
                    name: FieldName::from("busy"),
                    unit: Some(Unit::Microseconds),
                },
                Head {
                    name: FieldName::from("busy"),
                    unit: Some(Unit::Milliseconds),
                },
                Head {
                    name: FieldName::from("hits"),
                    unit: Some(Unit::Ratio),
                },
                Head {
                    name: FieldName::from("occupancy"),
                    unit: Some(Unit::Count),
                },
                Head {
                    name: FieldName::from("note"),
                    unit: None,
                },
                Head {
                    name: FieldName::from("cost"),
                    unit: Some(Unit::Count),
                },
                Head {
                    name: FieldName::from("cost"),
                    unit: Some(Unit::Count),
                },
            ]),
            rows: Vec::new(),
        }]),
    };
    let declarations = [
        (
            "f",
            Warrant::Replayed,
            (1234_u64, NOW, "1.23k"),
            ("120", "2.50"),
            (3_u64, 4_u64, "3/4"),
            Datum::Absent,
            (10_u64, 12_u64, "10", "12"),
        ),
        (
            "g",
            Warrant::Pending,
            (7_u64, Revision(1_i64), "7"),
            ("80", "1.25"),
            (0_u64, 1_u64, "0/1"),
            note,
            (3_u64, 3_u64, "3", "3"),
        ),
    ];
    for (record, (name, warrant, judgements, busy, hits, noted, cost)) in
        declarations.into_iter().enumerate()
    {
        let place = |field| Place { record, field };
        frame.records.push(Record {
            fields: Vec::from([
                field(
                    FieldName::from("name"),
                    Datum::Text(String::from(name)),
                    NOW,
                ),
                field(FieldName::from("warrant"), Datum::Warrant(warrant), NOW),
                field(
                    FieldName::from("judgements"),
                    Datum::Count(Count(judgements.0)),
                    judgements.1,
                ),
                field(
                    FieldName::from("busy"),
                    Datum::Latency {
                        p50: Duration::from_micros(120),
                        p99: Duration::from_micros(2500),
                        window: Duration::from_secs(1),
                    },
                    NOW,
                ),
                field(
                    FieldName::from("hits"),
                    Datum::Ratio {
                        hits: Count(hits.0),
                        total: Count(hits.1),
                    },
                    NOW,
                ),
                field(
                    FieldName::from("occupancy"),
                    Datum::Samples(samples.clone()),
                    NOW,
                ),
                field(FieldName::from("note"), noted.clone(), NOW),
                field(
                    FieldName::from("cost"),
                    Datum::Comparison {
                        before: Count(cost.0),
                        after: Count(cost.1),
                    },
                    NOW,
                ),
            ]),
        });
        let stale = judgements.1 < NOW;
        let mut counted = Cell::numeral(place(2), numeral!(judgements.2, Unit::Count));
        if stale {
            counted
                .attributes
                .push(Attribute::Hue(Warrant::Pending.colour()));
        }
        let (spelled, underlined) = match noted {
            Datum::Text(text) => (text, None),
            Datum::Marked { text, run } => (text, Some(Attribute::Underline(run))),
            Datum::Absent
            | Datum::Count(_)
            | Datum::Duration { .. }
            | Datum::Bytes(_)
            | Datum::Latency { .. }
            | Datum::Ratio { .. }
            | Datum::Samples(_)
            | Datum::Warrant(_)
            | Datum::Comparison { .. } => (String::new(), None),
        };
        let last = numeral!("31", Unit::Count);
        let row = Row {
            cells: Vec::from([
                Cell::text(place(0), String::from(name)),
                Cell {
                    place: Some(place(1)),
                    glyph: Some(warrant.glyph()),
                    warrant: Some(warrant),
                    attributes: Vec::from([Attribute::Hue(warrant.colour())]),
                    ..Cell::blank()
                },
                counted,
                Cell::numeral(place(3), numeral!(busy.0, Unit::Microseconds)),
                Cell::numeral(place(3), numeral!(busy.1, Unit::Milliseconds)),
                Cell::numeral(place(4), numeral!(hits.2, Unit::Ratio)),
                Cell {
                    place: Some(place(5)),
                    text: alloc::format!("{blocks} {}", last.text),
                    sparkline: Some(Sparkline {
                        cells: blocks.clone(),
                        last,
                        scale: numeral!("31", Unit::Count),
                        window: numeral!("32", Unit::Count),
                    }),
                    align: super::Align::Right,
                    ..Cell::blank()
                },
                Cell {
                    attributes: underlined.into_iter().collect(),
                    ..Cell::text(place(6), spelled)
                },
                Cell::numeral(place(7), numeral!(cost.2, Unit::Count)),
                Cell::numeral(place(7), numeral!(cost.3, Unit::Count)),
            ]),
        };
        if let Some(pane) = rendering.panes.get_mut(1) {
            pane.rows.push(row);
        }
    }
    if let Some(pane) = rendering.panes.get_mut(0) {
        let named = Place {
            record: 0,
            field: 0,
        };
        pane.rows.push(Row {
            cells: Vec::from([
                Cell::label(named, FieldName::from("name")),
                Cell::text(named, String::from("f")),
            ]),
        });
    }
    (frame, rendering)
}

#[test]
fn the_palette_is_the_blueprint_s()
{
    let drawn: Vec<(&str, &str)> = WARRANTS
        .iter()
        .map(|warrant| {
            (
                <&str>::from(warrant.glyph()),
                <&str>::from(warrant.colour()),
            )
        })
        .collect();
    assert_eq!(drawn, [
        ("·", "gandr.warrant.pending"),
        ("✓", "gandr.warrant.checked"),
        ("✓✓", "gandr.warrant.replayed"),
        ("✗", "gandr.warrant.refused"),
        ("○", "gandr.warrant.withheld"),
    ]);
}

#[test]
fn a_count_reads_as_three_significant_digits()
{
    for (count, text) in [
        (0_u64, "0"),
        (999_u64, "999"),
        (1000_u64, "1.00k"),
        (1234_u64, "1.23k"),
        (12_345_u64, "12.3k"),
        (123_456_u64, "123k"),
        (999_999_u64, "999k"),
        (1_000_000_u64, "1.00M"),
        (u64::MAX, "18.4E"),
    ] {
        let drawn = Numeral::from(Count(count));
        assert_eq!(drawn, numeral!(text, Unit::Count), "{count}");
        assert_eq!(patterned(&drawn), Some(()), "{count} keeps its pattern");
    }
}

#[test]
fn a_numeral_matches_one_pattern_per_unit()
{
    for (text, unit) in [
        ("0", Unit::Count),
        ("1.00k", Unit::Count),
        ("999", Unit::Microseconds),
        ("0.25", Unit::Microseconds),
        ("12300", Unit::Milliseconds),
        ("1020", Unit::Bytes),
        ("1.5", Unit::Kibibytes),
        ("40.9", Unit::Mebibytes),
        ("0/1", Unit::Ratio),
    ] {
        assert_eq!(patterned(&numeral!(text, unit)), Some(()), "{text}");
    }
    for (text, unit) in [
        ("1234", Unit::Count),
        ("1000k", Unit::Count),
        ("1kk", Unit::Count),
        ("01", Unit::Count),
        ("1.", Unit::Count),
        ("1.234", Unit::Milliseconds),
        ("1000", Unit::Microseconds),
        ("1024", Unit::Bytes),
        ("1k", Unit::Bytes),
        ("٣", Unit::Count),
        ("0.75", Unit::Ratio),
        ("03/4", Unit::Ratio),
    ] {
        assert_eq!(patterned(&numeral!(text, unit)), None, "{text}");
    }
}

#[test]
fn a_rendering_that_keeps_the_language_breaks_no_rule()
{
    let (before, earlier) = example(Datum::Text(String::from("due")));
    let (frame, rendering) = example(Datum::Text(String::from("owed")));
    assert_eq!(
        conform(&Shown {
            frame: &frame,
            rendering: &rendering,
            before: Some((&before, &earlier)),
        }),
        []
    );
    assert_eq!(
        conform(&Shown {
            frame: &Frame::default(),
            rendering: &Rendering::default(),
            before: None,
        }),
        [],
        "an empty frame renders as nothing"
    );
}

/// A change that breaks one rule of an example's rendering.
type Breaking = fn(&mut Frame, &mut Rendering);

#[test]
fn each_rule_refuses_the_rendering_that_breaks_it()
{
    macro_rules! at {
        ($pane:literal, $row:literal, $cell:literal) => {
            At {
                pane: $pane,
                row: $row,
                cell: $cell,
            }
        };
    }
    let cases: [(&str, Breaking); 20] = [
        ("ink-is-data", |frame, _| *frame = Frame::default()),
        ("no-decoration", |_, rendering| {
            cell(rendering, at!(1, 0, 0))
                .attributes
                .push(Attribute::Border);
        }),
        ("hue-is-warrant", |_, rendering| {
            cell(rendering, at!(1, 0, 2))
                .attributes
                .push(Attribute::Hue(Colour::from("red")));
        }),
        ("lightness-carries-nothing", |_, rendering| {
            cell(rendering, at!(1, 0, 2))
                .attributes
                .push(Attribute::Faint);
        }),
        ("quantity-is-length", |_, rendering| {
            *cell(rendering, at!(1, 0, 2)) = Cell::text(
                Place {
                    record: 0,
                    field: 2,
                },
                String::from("1.23k"),
            );
        }),
        ("small-multiples", |_, rendering| {
            if let Some(ref mut sparkline) = cell(rendering, at!(1, 1, 6)).sparkline {
                sparkline.scale = numeral!("9", Unit::Count);
            }
        }),
        ("sparklines", |_, rendering| {
            if let Some(ref mut sparkline) = cell(rendering, at!(1, 0, 6)).sparkline {
                sparkline.cells.push('▁');
            }
        }),
        ("numerals", |_, rendering| {
            *cell(rendering, at!(1, 0, 2)) = Cell::numeral(
                Place {
                    record: 0,
                    field: 2,
                },
                numeral!("1234", Unit::Count),
            );
        }),
        ("latency-is-two-numbers", |_, rendering| {
            *cell(rendering, at!(1, 0, 4)) = Cell::blank();
        }),
        ("ratio-is-a-pair", |_, rendering| {
            *cell(rendering, at!(1, 0, 5)) = Cell::numeral(
                Place {
                    record: 0,
                    field: 4,
                },
                numeral!("4/3", Unit::Ratio),
            );
        }),
        ("change-in-place", |_, rendering| {
            cell(rendering, at!(1, 0, 0))
                .attributes
                .push(Attribute::Bold);
        }),
        ("density", |_, rendering| {
            if let Some(pane) = rendering.panes.get_mut(1) {
                pane.rows.push(Row {
                    cells: Vec::from([const { Cell::blank() }; 10]),
                });
            }
        }),
        ("alignment", |_, rendering| {
            cell(rendering, at!(1, 0, 2)).align = super::Align::Left;
        }),
        ("stale-is-pending", |_, rendering| {
            cell(rendering, at!(1, 1, 2)).attributes.clear();
        }),
        ("glyph-twins-hue", |_, rendering| {
            cell(rendering, at!(1, 0, 1)).glyph = None;
        }),
        ("labels-are-field-names", |_, rendering| {
            cell(rendering, at!(0, 0, 0)).text = String::from("Name:");
        }),
        ("absence-is-blank", |_, rendering| {
            cell(rendering, at!(1, 0, 7)).text = String::from("n/a");
        }),
        ("document-order", |_, rendering| {
            if let Some(pane) = rendering.panes.get_mut(1) {
                pane.rows.reverse();
            }
        }),
        ("comparison-in-eye-span", |_, rendering| {
            *cell(rendering, at!(1, 0, 9)) = Cell::blank();
        }),
        ("one-meaning-per-glyph", |_, rendering| {
            cell(rendering, at!(1, 0, 0)).glyph = Some(Warrant::Refused.glyph());
        }),
    ];
    let (before, earlier) = example(Datum::Text(String::from("owed")));
    for (slug, broken) in cases {
        let (mut frame, mut rendering) = example(Datum::Text(String::from("owed")));
        broken(&mut frame, &mut rendering);
        let breaches = conform(&Shown {
            frame: &frame,
            rendering: &rendering,
            before: Some((&before, &earlier)),
        });
        assert!(
            breaches
                .iter()
                .any(|breach| <&str>::from(breach.rule) == slug),
            "{slug}: {breaches:?}"
        );
    }
}

#[test]
fn a_rendering_that_paints_a_border_breaks_no_decoration()
{
    let (frame, mut drawn) = example(Datum::Absent);
    if let Some(pane) = drawn.panes.get_mut(1) {
        pane.rows.insert(0, Row {
            cells: core::iter::repeat_with(|| Cell {
                text: String::from("────"),
                ..Cell::blank()
            })
            .take(10)
            .collect(),
        });
    }
    let (_, mut outlined) = example(Datum::Absent);
    cell(&mut outlined, At {
        pane: 1,
        row: 0,
        cell: 0,
    })
    .attributes
    .push(Attribute::Border);
    for rendering in [&drawn, &outlined] {
        let breaches = conform(&Shown {
            frame: &frame,
            rendering,
            before: None,
        });
        assert!(
            breaches
                .iter()
                .any(|breach| <&str>::from(breach.rule) == "no-decoration"),
            "{breaches:?}"
        );
    }
}

#[test]
fn an_underline_marks_only_the_run_its_datum_marks()
{
    let run = |start: usize, end: usize| {
        ByteRange::new(ByteOffset::from(start), ByteOffset::from(end)).expect("an ordered run")
    };
    let marked = Datum::Marked {
        text: String::from("(n : Nat, m : Nat) -> -F Nat"),
        run: run(10, 17),
    };
    let (frame, rendering) = example(marked.clone());
    assert_eq!(
        conform(&Shown {
            frame: &frame,
            rendering: &rendering,
            before: None,
        }),
        [],
        "the run that the datum marks is underlined"
    );
    let moved: Breaking = |_, rendering| {
        let held = cell(rendering, At {
            pane: 1,
            row: 1,
            cell: 7,
        });
        held.attributes = Vec::from([Attribute::Underline(
            ByteRange::new(ByteOffset::from(1_usize), ByteOffset::from(2_usize))
                .expect("an ordered run"),
        )]);
    };
    let elsewhere: Breaking = |_, rendering| {
        cell(rendering, At {
            pane: 1,
            row: 0,
            cell: 0,
        })
        .attributes
        .push(Attribute::Underline(
            ByteRange::new(ByteOffset::from(0_usize), ByteOffset::from(1_usize))
                .expect("an ordered run"),
        ));
    };
    for (broken, why) in [
        (moved, "a run other than the marked one"),
        (elsewhere, "a text that marks no run"),
    ] {
        let (mut frame, mut rendering) = example(marked.clone());
        broken(&mut frame, &mut rendering);
        let breaches = conform(&Shown {
            frame: &frame,
            rendering: &rendering,
            before: None,
        });
        assert!(
            breaches
                .iter()
                .any(|breach| <&str>::from(breach.rule) == "no-decoration"),
            "{why}: {breaches:?}"
        );
    }
}

#[test]
fn a_time_and_a_size_read_as_three_significant_digits()
{
    for (value, unit, text) in [
        (0_u64, Unit::Microseconds, "0"),
        (45_u64, Unit::Microseconds, "0.0450"),
        (999_u64, Unit::Microseconds, "0.999"),
        (1_000_u64, Unit::Microseconds, "1.00"),
        (12_345_u64, Unit::Microseconds, "12.3"),
        (999_999_u64, Unit::Microseconds, "999"),
        (1_000_000_u64, Unit::Milliseconds, "1.00"),
        (1_234_567_890_u64, Unit::Milliseconds, "1230"),
        (1_023_u64, Unit::Bytes, "1020"),
        (1_536_u64, Unit::Kibibytes, "1.50"),
        (5_242_880_u64, Unit::Mebibytes, "5.00"),
    ] {
        let drawn = Numeral::of(Count(value), unit);
        assert_eq!(drawn, numeral!(text, unit), "{value} in {unit:?}");
        assert_eq!(patterned(&drawn), Some(()), "{value} keeps its pattern");
    }
}

#[test]
fn a_ring_draws_thirty_two_cells_and_its_last_value()
{
    let full = Samples::new(SampleUnit::Count, (0_u64 .. 32_u64).map(Count).collect())
        .expect("a ring of 32 samples");
    let drawn = Sparkline::of(&full, Count(31), Unit::Count).expect("a full ring draws");
    assert_eq!(drawn.cells.chars().count(), SAMPLES);
    assert_eq!(drawn.cells.chars().next(), Some('▁'), "the lowest sample");
    assert_eq!(
        drawn.cells.chars().last(),
        Some('█'),
        "the sample at the scale"
    );
    assert_eq!(drawn.last, numeral!("31", Unit::Count));
    assert_eq!(drawn.window, numeral!("32", Unit::Count));
    let three = Samples::new(
        SampleUnit::Nanoseconds,
        Vec::from([Count(5_000), Count(10_000), Count(20_000)]),
    )
    .expect("a ring of three samples");
    let drawn = Sparkline::of(&three, Count(20_000), Unit::Microseconds)
        .expect("a ring of three samples draws");
    let unfilled: String = core::iter::repeat_n('▁', 29).collect();
    assert_eq!(drawn.cells, alloc::format!("{unfilled}▃▅█"));
    assert_eq!(drawn.last, numeral!("20.0", Unit::Microseconds));
    assert_eq!(drawn.scale, numeral!("20.0", Unit::Microseconds));
    let empty = Samples::new(SampleUnit::Count, Vec::new()).expect("an empty ring");
    assert_eq!(Sparkline::of(&empty, Count(0), Unit::Count), None);
    let (frame, mut rendering) = example(Datum::Absent);
    for row in 0 .. 2 {
        let at = At {
            pane: 1,
            row,
            cell: 6,
        };
        let line = Sparkline::of(&full, Count(31), Unit::Count).expect("a full ring draws");
        let drawing = cell(&mut rendering, at);
        drawing.text = alloc::format!("{} {}", line.cells, line.last.text);
        drawing.sparkline = Some(line);
    }
    let breaches = conform(&Shown {
        frame: &frame,
        rendering: &rendering,
        before: None,
    });
    assert!(breaches.is_empty(), "{breaches:?}");
}

#[test]
fn a_ring_holds_at_most_thirty_two_samples()
{
    let values = |count: u64| (0 .. count).map(Count).collect::<Vec<Count>>();
    let ring = Samples::new(SampleUnit::Count, values(32)).expect("32 values fit a ring");
    assert_eq!(ring.ceiling(), None, "a ring states no ceiling of its own");
    let full = <[Count; SAMPLES]>::try_from(values(32)).expect("32 values fill a ring");
    let bounded = Samples::bounded(SampleUnit::Count, full, Count(40));
    assert_eq!(
        (bounded.values(), bounded.ceiling()),
        (ring.values(), Some(Count(40))),
        "a bounded ring holds its 32 values under its ceiling"
    );
    assert_eq!(
        Samples::bounded(SampleUnit::Count, full, Count(0)).ceiling(),
        None,
        "a zero ceiling bounds no value"
    );
    let decoded: Samples =
        serde_json::from_value(serde_json::to_value(&bounded).expect("a ring encodes"))
            .expect("a bounded ring decodes");
    assert_eq!(decoded, bounded, "the ceiling survives the round trip");
    assert!(
        serde_json::to_value(&ring)
            .expect("a ring encodes")
            .get("ceiling")
            .is_none(),
        "a ring with no ceiling takes no bytes for it"
    );
    assert_eq!(
        Samples::new(SampleUnit::Count, values(33)),
        Err(TooManySamples { offered: 33 })
    );
    let image = |count: u64| serde_json::json!({ "unit": "Count", "values": values(count) });
    assert!(serde_json::from_value::<Samples>(image(32)).is_ok());
    assert!(serde_json::from_value::<Samples>(image(33)).is_err());
}
