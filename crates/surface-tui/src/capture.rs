//! The capture of a rendering as SVG: the lines that the side view lays out,
//! drawn on a grid of monospace cells.
//!
//! [`svg`] reads the lines that the terminal painter reads, so the widths, the
//! padding and the alignment of a capture are the view's own, and a change to
//! the layout changes the capture. Each line is one `<text>`, and each cell is
//! one `<tspan>` at the start of its column, so a font with other advances
//! keeps the columns. A hue is a class named for its warrant's colour, and the
//! class reads the CSS variable of the same name, with a light and a dark
//! default. So a host binds its own theme. The class states its light colour,
//! and a renderer with CSS variables reads the variable in its place. A capture
//! holds no time and no path, so one rendering always gives the same bytes,
//! and a diff of two captures shows the cells that moved.

use alloc::string::String;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_render_remote::Attribute;
use gandr_surface_render_remote::Colour;
use gandr_surface_render_remote::Pane;
use gandr_surface_render_remote::Warrant;
use ratatui::text::Span;

use crate::follow::laid;
use crate::follow::underlined;

/// The advance of one monospace cell, in pixels: three fifths of [`FONT`].
const ADVANCE: usize = 9;

/// The size of the font, in pixels.
const FONT: usize = 15;

/// The height of one line, in pixels.
const LEADING: usize = 20;

/// The distance from the top of a line to its baseline, in pixels.
const ASCENT: usize = 15;

/// The margin around the lines, in pixels.
const MARGIN: usize = 10;

/// The colour of the text that no hue names, light and dark.
const INK: [&str; 2] = ["#1f2328", "#e6edf3"];

/// The light and the dark default of each warrant's hue, as the terminal theme
/// paints it: a checked mark takes the colour of the text.
const SHADES: [(Warrant, [&str; 2]); 5] = [
    (Warrant::Pending, ["#6e7781", "#8b949e"]),
    (Warrant::Checked, INK),
    (Warrant::Replayed, ["#1a7f37", "#3fb950"]),
    (Warrant::Refused, ["#cf222e", "#f85149"]),
    (Warrant::Withheld, ["#9a6700", "#d29922"]),
];

/// Write the CSS name of `colour` into `out`: its dotted name with each dot a
/// dash, so `gandr.warrant.checked` is `gandr-warrant-checked`.
///
/// # Specification
/// trivial.
fn named(
    out: &mut String,
    colour: Colour,
)
{
    out.extend(
        <&str>::from(colour)
            .chars()
            .map(|letter| if letter == '.' { '-' } else { letter }),
    );
}

/// The SVG capture of `panes`, a run of the panes of a rendering, as the side
/// view lays them out.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one SVG document. Each line of the view's layout is one `<text>`
///   at its row, and each cell that shows a letter is one `<tspan>` at its
///   first letter's column, so an indented cell starts at its depth. The
///   padding of a cell is not written. A hue is the class of its colour's name,
///   bold and italic are the font's weight and style, an underline is a
///   `<tspan>` inside the cell's own with the text decoration over its run, and
///   the rules refuse every other attribute. Each warrant's class reads the CSS
///   variable of its name, with a light and a dark default. The canvas has no
///   background.
/// - provides: the rendered capture of a pane, which a test compares with the
///   committed file.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the recorded frames of a scene give their committed
///   capture; a change of one column's width moves the cells after it, and the
///   comparison fails with the lines that moved.
/// - witness: `tests::captures::the_warrants_scene_renders_as_its_captures`
/// - witness: `tests::captures::the_schedule_scene_renders_as_its_capture`
/// - witness: `tests::captures::the_stack_scene_renders_as_its_captures`
/// - witness: `tests::captures::the_derivation_scene_renders_as_its_captures`
#[spec(ensures: |ret| ret.starts_with("<svg ") && ret.ends_with("</svg>\n"))]
#[inline]
#[must_use]
pub fn svg(panes: &[Pane]) -> String
{
    let lines = laid(panes);
    let columns = lines
        .iter()
        .map(|line| {
            line.iter()
                .map(|&(ref text, _)| Span::raw(text.as_str()).width())
                .fold(line.len().saturating_sub(1), usize::saturating_add)
        })
        .max()
        .unwrap_or_default();
    let width = columns
        .saturating_mul(ADVANCE)
        .saturating_add(MARGIN.saturating_mul(2));
    let height = lines
        .len()
        .saturating_mul(LEADING)
        .saturating_add(MARGIN.saturating_mul(2));
    let mut out = String::new();
    let _written = write!(
        out,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" \
         viewBox=\"0 0 {width} {height}\" font-family=\"ui-monospace, SFMono-Regular, Menlo, \
         Consolas, monospace\" font-size=\"{FONT}\" xml:space=\"preserve\">\n<style>\n"
    );
    for (scheme, shade) in [("", 0_usize), ("@media (prefers-color-scheme: dark) { ", 1)] {
        let ink = INK.get(shade).copied().unwrap_or_default();
        let _written = write!(out, "{scheme}svg {{ color: {ink};");
        for &(warrant, ref shades) in &SHADES {
            out.push_str(" --");
            named(&mut out, warrant.colour());
            let _written = write!(out, ": {};", shades.get(shade).copied().unwrap_or_default());
        }
        out.push_str(if scheme.is_empty() { " }\n" } else { " } }\n" });
    }
    out.push_str("text { fill: currentColor; }\n");
    for &(warrant, ref shades) in &SHADES {
        out.push('.');
        named(&mut out, warrant.colour());
        let light = shades.first().copied().unwrap_or_default();
        let _written = writeln!(out, " {{ fill: {light}; }}");
    }
    out.push_str("@supports (fill: var(--gandr-warrant-checked)) {\n");
    for &(warrant, _) in &SHADES {
        out.push('.');
        named(&mut out, warrant.colour());
        out.push_str(" { fill: var(--");
        named(&mut out, warrant.colour());
        out.push_str("); }\n");
    }
    out.push_str("}\n</style>\n");
    for (row, line) in lines.iter().enumerate() {
        let baseline = row
            .saturating_mul(LEADING)
            .saturating_add(MARGIN)
            .saturating_add(ASCENT);
        let _written = write!(out, "<text y=\"{baseline}\">");
        let mut column = 0_usize;
        for painted in line {
            let &(ref text, cell) = painted;
            let shown = text.trim_matches(' ');
            let indent = text
                .len()
                .saturating_sub(text.trim_start_matches(' ').len());
            if !shown.is_empty() {
                let x = column
                    .saturating_add(indent)
                    .saturating_mul(ADVANCE)
                    .saturating_add(MARGIN);
                let _written = write!(out, "<tspan x=\"{x}\"");
                for attribute in cell.iter().flat_map(|cell| &cell.attributes) {
                    match *attribute {
                        Attribute::Hue(colour) => {
                            out.push_str(" class=\"");
                            named(&mut out, colour);
                            out.push('"');
                        },
                        Attribute::Bold => out.push_str(" font-weight=\"bold\""),
                        Attribute::Italic => out.push_str(" font-style=\"italic\""),
                        Attribute::Faint
                        | Attribute::Opacity
                        | Attribute::Background(_)
                        | Attribute::Border
                        | Attribute::Blink
                        | Attribute::Underline(_)
                        | Attribute::Indent(_) => {},
                    }
                }
                out.push('>');
                let pieces = underlined(painted);
                let escaped = |out: &mut String, piece: &str| {
                    for letter in piece.chars() {
                        match letter {
                            '&' => out.push_str("&amp;"),
                            '<' => out.push_str("&lt;"),
                            '>' => out.push_str("&gt;"),
                            other => out.push(other),
                        }
                    }
                };
                if pieces.run.is_empty() {
                    escaped(&mut out, shown);
                }
                else {
                    escaped(&mut out, pieces.before.trim_start_matches(' '));
                    out.push_str("<tspan text-decoration=\"underline\">");
                    escaped(&mut out, pieces.run);
                    out.push_str("</tspan>");
                    escaped(&mut out, pieces.after.trim_end_matches(' '));
                }
                out.push_str("</tspan>");
            }
            column = column
                .saturating_add(Span::raw(text.as_str()).width())
                .saturating_add(1);
        }
        out.push_str("</text>\n");
    }
    out.push_str("</svg>\n");
    out
}
