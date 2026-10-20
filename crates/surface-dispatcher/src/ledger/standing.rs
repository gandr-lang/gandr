//! Which rules no source molds, and what says so.
//!
//! # Every reason is derived
//!
//! A rule is internal when no source can mold it, and the ledger lists it in a
//! table of its own with the reason and what the reason is read from; nothing
//! is listed by hand. The reasons, tried in this order:
//!
//! | Reason | Read from | When |
//! | ------ | --------- | ---- |
//! | layout | the labeler | every reading passes a tile whose text, labeled alone, opens with layout, as `/*` does |
//! | tileless | the grammar | the form holds no tile, so no tree names the rule |
//! | shadowed | the grammar | an earlier rule of the same sort reads every reading whole, or opens with it and requires nothing after it, and the molder commits that rule |
//! | captured | the labeler | the form requires one word, which the labeler also offers as a class a one-tile rule of the same sort reads |
//! | enclosed | a parser probe | the form is one class tile, and no probe text holding its class's sample molds the rule: alone in a slot of its sort, or enclosed in up to two other rules' holes |
//!
//! The probe parses each candidate text and asks whether a tile of the rule is
//! molded. The class's token and its probe text stand in the sort's slot;
//! each text of one depth then stands in every hole of its sort in every
//! other rule's shortest reading, which is the next depth, to
//! [`PROBE_DEPTH`]. A lexical class is the labeler's mode, and a mode one
//! rule opens can reach a hole another rule nests inside it, so one depth is
//! not enough: the shell's variable name is reached only inside a string's
//! interpolation inside a shell block. A context rule is spelled by its
//! shortest reading: an option or a repetition holding a hole of the probed
//! sort is taken once, every other is left out; an alternation takes its
//! first branch holding such a hole, else its shortest; a class tile is its
//! class's token from [`SAMPLES`]; another hole is a filler of its sort. A
//! class the table lacks is a fault, never a skip, so a new class names
//! itself.
//!
//! - Choice: reasons the grammar and the labeler decide wherever they can; the
//!   probe only for a lone class tile, whose reachability is the labeler's
//!   lexical modes, which the grammar does not carry.
//! - Alternatives: a list of dead rules beside the grammar, which is a hand
//!   list; the probe for every rule, which makes the grammar's own facts depend
//!   on a sampled spelling.
//! - Reversal: a rule the exemplar gate cannot show although no reason fires
//!   widens a reason here; a rule a reason hides although a source molds it
//!   narrows that reason.

use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RegexShape;
use gandr_surface_grammar::RegexView;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::Sym;
use gandr_surface_grammar::TileLabel;
use gandr_surface_parser::CandidateLabel;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::TileSpelling;
use gandr_surface_parser::TokenText;
use gandr_surface_parser::candidate_labels;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_parser::tile_spelling;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

use super::LedgerFault;
use super::Node;
use super::Standing;
use super::Visited;
use super::fold;

/// A lexical class's sample.
#[derive(Clone, Copy, Debug)]
pub(super) struct Sample
{
    /// The class.
    class: &'static str,
    /// The token a tile of the class is spelled by in a probe's context.
    token: &'static str,
    /// The text a probe writes for a rule that is the class alone: it holds
    /// the token where the labeler emits it.
    probe: &'static str,
}

/// Every lexical class of the grammar, with its sample.
const SAMPLES: &[Sample] = &[
    Sample {
        class: "character",
        token: "'c'",
        probe: "'c'",
    },
    Sample {
        class: "constructor",
        token: "C",
        probe: "C",
    },
    Sample {
        class: "double_string_fragment",
        token: "s",
        probe: "s",
    },
    Sample {
        class: "environment_assignment",
        token: "A=b",
        probe: "A=b",
    },
    Sample {
        class: "escape_sequence",
        token: "\\n",
        probe: "\"\\n\"",
    },
    Sample {
        class: "file_descriptor",
        token: "2",
        probe: "2>&1",
    },
    Sample {
        class: "hole_name",
        token: "h",
        probe: "h",
    },
    Sample {
        class: "identifier",
        token: "x",
        probe: "x",
    },
    Sample {
        class: "number",
        token: "1",
        probe: "1",
    },
    Sample {
        class: "shell_word",
        token: "w",
        probe: "w",
    },
    Sample {
        class: "single_quoted_content",
        token: "s",
        probe: "s",
    },
    Sample {
        class: "string_fragment",
        token: "s",
        probe: "s",
    },
    Sample {
        class: "type_identifier",
        token: "T",
        probe: "T",
    },
    Sample {
        class: "type_variable",
        token: "a",
        probe: "a",
    },
    Sample {
        class: "typed_number",
        token: "1i32",
        probe: "1i32",
    },
    Sample {
        class: "variable_name",
        token: "HOME",
        probe: "$HOME",
    },
];

/// Why no source molds a rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Internal
{
    /// Every reading passes `tile`, which the labeler reads as layout.
    Layout
    {
        /// The first such tile the form holds.
        tile: &'static str,
    },
    /// The form holds no tile.
    Tileless,
    /// Every reading is read by the earlier rule `by`.
    Shadowed
    {
        /// The rule the molder commits instead.
        by: &'static str,
    },
    /// The one required tile is a word the one-tile rule `by` reads as a
    /// class.
    Captured
    {
        /// The word.
        tile: &'static str,
        /// The rule reading it as a class.
        by: &'static str,
    },
    /// The form is one tile of `class`, which no probe molds as this rule.
    Enclosed
    {
        /// The class.
        class: &'static str,
    },
}

/// What a reason is read from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Evidence
{
    /// The grammar's forms.
    Grammar,
    /// The labeler, over a tile's own text.
    Labeler,
    /// The parser, over probe texts.
    ParserProbe,
}

impl core::fmt::Display for Evidence
{
    /// Writes `grammar`, `labeler` or `parser probe`.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::Grammar => "grammar",
            Self::Labeler => "labeler",
            Self::ParserProbe => "parser probe",
        })
    }
}

/// A reason's machine name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ReasonName(Internal);

impl core::fmt::Display for ReasonName
{
    /// Writes `layout`, `tileless`, `shadowed`, `captured` or `enclosed`.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match self.0 {
            Internal::Layout { .. } => "layout",
            Internal::Tileless => "tileless",
            Internal::Shadowed { .. } => "shadowed",
            Internal::Captured { .. } => "captured",
            Internal::Enclosed { .. } => "enclosed",
        })
    }
}

impl Internal
{
    /// What the reason is read from.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn evidence(self) -> Evidence
    {
        match self {
            Self::Layout { .. } | Self::Captured { .. } => Evidence::Labeler,
            Self::Tileless | Self::Shadowed { .. } => Evidence::Grammar,
            Self::Enclosed { .. } => Evidence::ParserProbe,
        }
    }

    /// The reason's machine name.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn name(self) -> ReasonName
    {
        ReasonName(self)
    }
}

impl core::fmt::Display for Internal
{
    /// Writes the reason as a sentence fragment.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Layout { tile } => {
                write!(f, "every reading passes `{tile}`, which is layout")
            },
            Self::Tileless => f.write_str("the form holds no tile, so no tree names the rule"),
            Self::Shadowed { by } => {
                write!(
                    f,
                    "every reading is read by `{by}`, which is committed instead"
                )
            },
            Self::Captured { tile, by } => write!(
                f,
                "its one required word `{tile}` is read as a class by `{by}`"
            ),
            Self::Enclosed { class } => write!(
                f,
                "no probe molds it: `{class}` is lexed only where another rule's tile takes it"
            ),
        }
    }
}

/// Whether a probe's reading holds the probed text.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Holds
{
    /// It does, in a hole of the probed sort.
    Probe,
    /// It does not.
    #[default]
    Nothing,
}

/// A context rule's shortest reading for a probe.
#[derive(Clone, Debug, Default)]
struct Reading
{
    /// The text.
    text: String,
    /// Whether it holds the probed text.
    holds: Holds,
}

/// Whether a probe text molds the probed rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Probed
{
    /// A tile of the rule is molded.
    Molded,
    /// None is.
    Unmolded,
}

/// The reason no source molds `rule`, or none.
///
/// # Specification
/// - requires: `rule` is a rule of `pbg`.
/// - ensures: the first reason of the module's table that holds, in table
///   order; [`Standing::Committed`] when none does.
/// - fails: a class the probe must spell has no sample.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Sample`] naming the class.
///
/// # Adequacy
/// - hypothesis: L3 — over the built-in grammar with one form per reason added,
///   each reason fires on its form; over the built-in grammar alone only the
///   type argument's coercion is internal, and every committed exemplar molds
///   its rule.
/// - witness: `ledger::tests::each_unmoldable_form_has_its_derived_reason`
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |standing| *standing == Standing::Committed || matches!(*standing, Standing::Internal(_))))]
pub(super) fn standing(
    pbg: &Pbg,
    rule: &Rule,
) -> Result<Standing, LedgerFault>
{
    let root = rule.regex().view();
    for derived in [
        layout(root),
        tileless(root),
        shadowed(pbg, rule),
        captured(pbg, rule),
    ] {
        if let Standing::Internal(reason) = derived {
            return Ok(Standing::Internal(reason));
        }
    }
    enclosed(pbg, rule)
}

/// [`Internal::Layout`] when every reading of `root` passes a layout tile.
///
/// # Specification
/// - requires: nothing.
/// - ensures: internal exactly when every reading passes a tile whose text,
///   labeled alone, opens with a layout token at its first byte, naming the
///   first such tile the form writes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a block comment form is internal through `/*`; every
///   built-in form is not.
/// - witness: `ledger::tests::each_unmoldable_form_has_its_derived_reason`
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
#[spec(ensures: |ret| ret == Standing::Committed || matches!(ret, Standing::Internal(Internal::Layout { .. })))]
fn layout(root: RegexView<'_>) -> Standing
{
    let is_layout = |tile: &str| match tile_spelling(CandidateLabel::from(tile)) {
        TileSpelling::Class(_) => false,
        TileSpelling::Literal(text) => label(SourceFragment::from(text))
            .first()
            .is_some_and(|token| token.start == 0 && matches!(token.lexeme, Lexeme::Space)),
    };
    let mut first: Option<&'static str> = None;
    let writable: Result<bool, ()> = fold(
        root,
        |_| Visited::Open,
        |node, children| {
            Ok(match node {
                Node::Tile(tile) => {
                    let blocked = is_layout(tile);
                    if blocked && first.is_none() {
                        first = Some(tile);
                    }
                    !blocked
                },
                Node::Seq => children.iter().all(|&writable| writable),
                Node::Alt => children.iter().any(|&writable| writable),
                Node::Empty | Node::Hole(_) | Node::Optional | Node::Repeat => true,
            })
        },
        (),
    );
    match (writable, first) {
        (Ok(false), Some(tile)) => Standing::Internal(Internal::Layout { tile }),
        (Ok(_) | Err(()), _) => Standing::Committed,
    }
}

/// [`Internal::Tileless`] when `root` holds no tile.
///
/// # Specification
/// - requires: nothing.
/// - ensures: internal exactly when no node of the form is a tile.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the type instantiation, a lone hole, is tileless; every
///   other built-in form holds a tile.
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
#[spec(ensures: |ret| ret == Standing::Committed || ret == Standing::Internal(Internal::Tileless))]
fn tileless(root: RegexView<'_>) -> Standing
{
    let tiled: Result<bool, ()> = fold(
        root,
        |_| Visited::Open,
        |node, children| Ok(matches!(node, Node::Tile(_)) || children.iter().any(|&tiled| tiled)),
        (),
    );
    match tiled {
        Ok(false) => Standing::Internal(Internal::Tileless),
        Ok(true) | Err(()) => Standing::Committed,
    }
}

/// The top-level alternatives of `view`: its branches, or itself.
///
/// # Specification
/// trivial.
fn alternatives(view: RegexView<'_>) -> Vec<RegexView<'_>>
{
    match view.shape() {
        RegexShape::Alt(branches) => branches,
        RegexShape::Empty
        | RegexShape::Sym(_)
        | RegexShape::Seq(_)
        | RegexShape::Optional(_)
        | RegexShape::Repeat(_) => vec![view],
    }
}

/// [`Internal::Shadowed`] when an earlier rule of `rule`'s sort reads every
/// reading of it.
///
/// # Specification
/// - requires: `rule` is a rule of `pbg`.
/// - ensures: internal, naming the earliest such rule, exactly when an earlier
///   rule of the same sort holds, for each top-level alternative of `rule`'s
///   form, a top-level alternative equal to it or a sequence opening with it
///   whose remaining parts are all options or repetitions.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a one-tile constructor pattern, which
///   `constructor_pattern` reads, is shadowed, and the identifier pattern,
///   which `cons_pattern` opens with but does not end at, is not.
/// - witness: `ledger::tests::each_unmoldable_form_has_its_derived_reason`
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
#[spec(ensures: |ret| ret == Standing::Committed || matches!(ret, Standing::Internal(Internal::Shadowed { .. })))]
fn shadowed(
    pbg: &Pbg,
    rule: &Rule,
) -> Standing
{
    let reads = |wide: RegexView<'_>, narrow: RegexView<'_>| {
        wide == narrow
            || match wide.shape() {
                RegexShape::Seq(parts) => parts.split_first().is_some_and(|(&head, rest)| {
                    head == narrow
                        && rest.iter().all(|part| {
                            matches!(
                                part.shape(),
                                RegexShape::Optional(_) | RegexShape::Repeat(_)
                            )
                        })
                }),
                RegexShape::Empty
                | RegexShape::Sym(_)
                | RegexShape::Alt(_)
                | RegexShape::Optional(_)
                | RegexShape::Repeat(_) => false,
            }
    };
    let own = alternatives(rule.regex().view());
    for earlier in pbg
        .rules()
        .iter()
        .take_while(|other| other.name != rule.name)
    {
        if earlier.sort != rule.sort {
            continue;
        }
        let wide = alternatives(earlier.regex().view());
        let covered = own
            .iter()
            .all(|&narrow| wide.iter().any(|&branch| reads(branch, narrow)));
        if covered {
            return Standing::Internal(Internal::Shadowed { by: earlier.name });
        }
    }
    Standing::Committed
}

/// [`Internal::Captured`] when `rule` requires one word the labeler also
/// offers as a class a one-tile rule of its sort reads.
///
/// # Specification
/// - requires: `rule` is a rule of `pbg`.
/// - ensures: internal exactly when the form, its options and repetitions left
///   out, is one literal tile whose text labels as one word token, and the
///   labeler offers that token a label other than its own text that the only
///   tile of another rule of the same sort carries.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a shell form whose word reads as an identifier is
///   captured; the reserved `unit`, whose word the labeler reads as itself, is
///   not.
/// - witness: `ledger::tests::each_unmoldable_form_has_its_derived_reason`
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
#[spec(ensures: |ret| ret == Standing::Committed || matches!(ret, Standing::Internal(Internal::Captured { .. })))]
fn captured(
    pbg: &Pbg,
    rule: &Rule,
) -> Standing
{
    // The tiles every reading requires, in order; a hole or an alternation
    // counts as two entries, so a form holding one is never a lone word.
    let required: Result<Vec<&'static str>, ()> = fold(
        rule.regex().view(),
        |_| Visited::Open,
        |node, children| {
            Ok(match node {
                Node::Tile(tile) => vec![tile],
                Node::Seq => children.concat(),
                Node::Hole(_) | Node::Alt | Node::Empty => vec![""; 2],
                Node::Optional | Node::Repeat => Vec::new(),
            })
        },
        (),
    );
    let Ok(required) = required
    else {
        return Standing::Committed;
    };
    let &[tile] = required.as_slice()
    else {
        return Standing::Committed;
    };
    let TileSpelling::Literal(text) = tile_spelling(CandidateLabel::from(tile))
    else {
        return Standing::Committed;
    };
    let tokens = label(SourceFragment::from(text));
    let &[token] = tokens.as_slice()
    else {
        return Standing::Committed;
    };
    let whole = token.start == 0
        && usize::try_from(token.end).is_ok_and(|end| end == text.len())
        && matches!(token.lexeme, Lexeme::LowerWord | Lexeme::UpperWord);
    if !whole {
        return Standing::Committed;
    }
    for &offered in &candidate_labels(token.lexeme, TokenText::from(text)) {
        let offered = <&str>::from(offered);
        if offered == text {
            continue;
        }
        let reader = pbg.rules().iter().find(|other| {
            other.name != rule.name
                && other.sort == rule.sort
                && matches!(other.regex().view().shape(), RegexShape::Sym(Sym::Tile(only)) if only.label == offered)
        });
        if let Some(reader) = reader {
            return Standing::Internal(Internal::Captured {
                tile,
                by: reader.name,
            });
        }
    }
    Standing::Committed
}

/// How many rules deep the probe encloses a class's sample: the rule's own
/// slot, then one enclosing rule, then two. Two reaches a lexical mode one
/// rule opens and another reads inside, as the shell block's mode reaches an
/// interpolation inside a string.
const PROBE_DEPTH: u8 = 2;

/// Whether the labeler emits a token a class tile can take.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Emits
{
    /// Some token of the text is offered the class's label.
    Class,
    /// None is.
    Other,
}

/// Whether labeling `text` offers some token the label `class`.
///
/// # Specification
/// trivial.
fn emits(
    text: SourceFragment<'_>,
    class: TileLabel,
) -> Emits
{
    let whole = <&str>::from(text);
    let offered = label(text).iter().any(|token| {
        let span = usize::try_from(token.start)
            .ok()
            .zip(usize::try_from(token.end).ok())
            .and_then(|(start, end)| whole.get(start .. end));
        span.is_some_and(|spelled| {
            candidate_labels(token.lexeme, TokenText::from(spelled))
                .iter()
                .any(|&candidate| <&str>::from(candidate) == class.0)
        })
    });
    if offered { Emits::Class } else { Emits::Other }
}

/// [`Internal::Enclosed`] when `rule` is one class tile no probe molds.
///
/// # Specification
/// - requires: `rule` is a rule of `pbg`.
/// - ensures: internal exactly when the form is one class tile and no probe
///   text holds a tile molded by the rule. The probe texts are the class's
///   token and its probe text, each in its sort's slot; then each text of one
///   depth stands in every hole of its sort in every other rule's shortest
///   reading, in that rule's slot, to [`PROBE_DEPTH`]. Past the first enclosure
///   a reading is probed only where the labeler offers the class a token it
///   does not offer in the enclosed text alone: a deeper rule matters only by
///   the lexical mode it opens.
/// - fails: a class a probe spells has no sample.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Sample`] naming the class.
///
/// # Adequacy
/// - hypothesis: L3 — a lone escape sequence is enclosed; the shell variable
///   name, reached two rules deep inside a string's interpolation inside a
///   shell block, the shell word, reached through the shell block's hole, and
///   the identifier, reached alone, are not.
/// - witness: `ledger::tests::each_unmoldable_form_has_its_derived_reason`
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |standing| *standing == Standing::Committed || matches!(*standing, Standing::Internal(Internal::Enclosed { .. }))))]
fn enclosed(
    pbg: &Pbg,
    rule: &Rule,
) -> Result<Standing, LedgerFault>
{
    let RegexShape::Sym(Sym::Tile(only)) = rule.regex().view().shape()
    else {
        return Ok(Standing::Committed);
    };
    let TileSpelling::Class(class) = tile_spelling(CandidateLabel::from(only.label))
    else {
        return Ok(Standing::Committed);
    };
    let sample = sample(TileLabel(class))?;
    let mut frontier: BTreeSet<(Sort, String)> = [sample.token, sample.probe]
        .into_iter()
        .map(|text| (rule.sort, text.to_owned()))
        .collect();
    for depth in 0 ..= PROBE_DEPTH {
        for &(sort, ref text) in &frontier {
            if molds(pbg, rule, SourceText::from(slot(sort, text).as_str())) == Probed::Molded {
                return Ok(Standing::Committed);
            }
        }
        if depth == PROBE_DEPTH {
            break;
        }
        let mut enclosing = BTreeSet::new();
        for &(sort, ref text) in &frontier {
            let enclosed_alone = emits(SourceFragment::from(text.as_str()), TileLabel(only.label));
            for context in pbg.rules() {
                if context.name == rule.name {
                    continue;
                }
                let read = reading(context, sort, SourceFragment::from(text.as_str()))?;
                let opens_mode = depth == 0
                    || (enclosed_alone == Emits::Other
                        && emits(
                            SourceFragment::from(read.text.as_str()),
                            TileLabel(only.label),
                        ) == Emits::Class);
                if read.holds == Holds::Probe && opens_mode {
                    let _new = enclosing.insert((context.sort, read.text));
                }
            }
        }
        frontier = enclosing;
    }
    Ok(Standing::Internal(Internal::Enclosed { class }))
}

/// The sample of `class`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the [`SAMPLES`] row of `class`.
/// - fails: the table has no row for `class`.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Sample`] naming the class.
///
/// # Adequacy
/// - hypothesis: L3 — every class of the built-in grammar has a row, since the
///   ledger builds; a class outside the table is refused by name.
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |row| row.class == class.0))]
fn sample(class: TileLabel) -> Result<&'static Sample, LedgerFault>
{
    SAMPLES
        .iter()
        .find(|row| row.class == class.0)
        .ok_or(LedgerFault::Sample { class: class.0 })
}

/// `text` standing where a form of `sort` stands in a source.
///
/// # Specification
/// trivial.
fn slot(
    sort: Sort,
    text: impl core::fmt::Display,
) -> String
{
    match sort {
        Sort::Item => text.to_string(),
        Sort::ModuleMember => format!("module Probe {{ {text} }}"),
        Sort::Expression => format!("def probe = {text} ;"),
        Sort::Pattern => format!("def probe = case x {{ {text} => 1 }} ;"),
        Sort::Type => format!("def probe : {text} ;"),
        Sort::Instantiation => format!("def probe = f[{text}](1) ;"),
    }
}

/// The shortest reading of `context` holding `probe`'s text in every hole of
/// `sort`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the module's spelling of a context: an option or a repetition
///   holding a hole of `sort` once, every other left out; an alternation's
///   first branch holding one, else its shortest branch; class tiles as their
///   samples' tokens; other holes as fillers of their sorts; parts joined by a
///   space only between two word characters, so a quote touches what it
///   encloses.
/// - fails: a class tile has no sample.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Sample`] naming the class.
///
/// # Adequacy
/// - hypothesis: L3 — the shell block's reading holds the shell word's sample
///   and molds it.
/// - witness: `ledger::tests::every_internal_rule_has_its_derived_reason`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |read| read.holds == Holds::Nothing || read.text.contains(<&str>::from(probe))))]
fn reading(
    context: &Rule,
    sort: Sort,
    probe: SourceFragment<'_>,
) -> Result<Reading, LedgerFault>
{
    fold(
        context.regex().view(),
        |_| Visited::Open,
        |node, children: Vec<Reading>| {
            Ok(match node {
                Node::Empty => Reading::default(),
                Node::Hole(hole) if hole == sort => Reading {
                    text: <&str>::from(probe).to_owned(),
                    holds: Holds::Probe,
                },
                Node::Hole(hole) => Reading {
                    text: match hole {
                        Sort::Item => "def a = 1 ;",
                        Sort::ModuleMember => "def a = 1;",
                        Sort::Expression | Sort::Pattern => "x",
                        Sort::Type => "T",
                        Sort::Instantiation => "<",
                    }
                    .to_owned(),
                    holds: Holds::Nothing,
                },
                Node::Tile(tile) => Reading {
                    text: match tile_spelling(CandidateLabel::from(tile)) {
                        TileSpelling::Literal(text) => text.to_owned(),
                        TileSpelling::Class(class) => sample(TileLabel(class))?.token.to_owned(),
                    },
                    holds: Holds::Nothing,
                },
                Node::Seq => {
                    let holds = if children.iter().any(|child| child.holds == Holds::Probe) {
                        Holds::Probe
                    }
                    else {
                        Holds::Nothing
                    };
                    // A space only between two word characters: a string's
                    // quote and its interpolation must touch, as a lexical
                    // mode reads the bytes it is given.
                    let mut text = String::new();
                    for child in children {
                        let word = |character: Option<char>| {
                            character.is_some_and(|character| {
                                character.is_alphanumeric() || character == '_'
                            })
                        };
                        if word(text.chars().next_back()) && word(child.text.chars().next()) {
                            text.push(' ');
                        }
                        text.push_str(&child.text);
                    }
                    Reading { text, holds }
                },
                Node::Alt => {
                    let holding = children
                        .iter()
                        .position(|child| child.holds == Holds::Probe);
                    let shortest = children
                        .iter()
                        .enumerate()
                        .min_by_key(|&(_, child)| child.text.len())
                        .map(|(at, _)| at);
                    holding
                        .or(shortest)
                        .and_then(|at| children.into_iter().nth(at))
                        .unwrap_or_default()
                },
                Node::Optional | Node::Repeat => children
                    .into_iter()
                    .find(|child| child.holds == Holds::Probe)
                    .unwrap_or_default(),
            })
        },
        LedgerFault::Molds { rule: context.name },
    )
}

/// Whether `text` parses to a tree holding a tile molded by `rule`.
///
/// # Specification
/// trivial.
fn molds(
    pbg: &Pbg,
    rule: &Rule,
    text: SourceText<'_>,
) -> Probed
{
    let Ok(parsed) = parse(pbg, text)
    else {
        return Probed::Unmolded;
    };
    let tree = parsed.tree();
    let molded = tree.positions().any(|position| {
        tree.node(position).is_some_and(|node| match node.label() {
            NodeLabel::Tile(mold) => pbg
                .rule_of(mold)
                .is_ok_and(|molded| molded.name == rule.name),
            NodeLabel::Wald
            | NodeLabel::Meld(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space
            | NodeLabel::Doc => false,
        })
    });
    if molded {
        Probed::Molded
    }
    else {
        Probed::Unmolded
    }
}
