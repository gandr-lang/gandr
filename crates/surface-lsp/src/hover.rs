//! What a hover shows: the type of whatever the cursor is in, and a
//! declaration's documentation.
//!
//! # A hover answers the innermost node
//!
//! A hover reads the declarations the text's [`Reading`] holds — those the
//! outline reads off the tree, each with its declaring form's key — and the
//! document's type table (`TypeTable`), which [`hovering`] builds once per
//! revision of the copy and the copy keeps until it changes. It answers, in
//! order:
//!
//! - **A declaration's name** — from its first character to just past its last
//!   — with a fenced `gandr` block holding the name and, when the table types
//!   the declaration, ` : ` and its type, then the documentation the session's
//!   latest accepted lowering filed for the declaring form, after a blank line,
//!   about the name's range. The table keys a declaration by each of its forms,
//!   so a signature and the definition completing it both answer the one
//!   declaration they make. A theory, a module and a declaration the table does
//!   not type answer as written instead: the head up to the brace opening its
//!   body — a module's ascription included — and, for a theory, its members
//!   between braces, one to a line, an `include` among them unflattened.
//! - **A member a theory, a family or a codata declaration writes** among its
//!   own tiles — on its name when nothing inside it is typed, and anywhere in
//!   it when the only entry there is its holder's — as written, without the
//!   body a rule fills; an `include` likewise.
//! - **The innermost typed node holding the cursor**, about its span: a term
//!   with its type, and, when an outer judgement checked it against a type
//!   spelled otherwise, that type after it; a binder with its name and the type
//!   of its uses; a written type with its text and its universe; a term the
//!   source writes as one name — a use, a constructor, a member — with that
//!   name before its type, as its binder answers. A keyword or a delimiter
//!   inside a term answers that term, so `return` and `{` answer the
//!   computation they open. A node spanning a whole declaration — the body's
//!   term the lowering writes over its declaration — answers as that
//!   declaration's name does, about its head when the cursor is there.
//! - **The head of the innermost declaration holding the cursor** — from its
//!   declaring form's start to the brace opening its own body, or all of it
//!   when it has none — about the head, as for its name: the keyword that
//!   introduces it, the colon of its signature, a module's ascription, the
//!   layout before its body. A member's keyword answers the member. An
//!   attribute before the head answers the same, about the attributes. Inside a
//!   body, a member answers by its own entries, and a position no entry holds
//!   answers nothing, rather than the declaration around it.
//!
//! A position in no declaration's head hovers nothing, and so does a document
//! whose grammar did not build. Every type is spelled through the shared
//! printer at 80 columns.
//!
//! The alternative was to look the name under the cursor up among the
//! session's items by its occurrence among the document's declarations: it
//! answers declaration names only, and counts a signature and its definition
//! as two occurrences of one item. The choice reverses when the session keeps
//! the typed run's table itself, and the hover then reads it there rather than
//! judging the copy's text again.
//!
//! # The table is typed over the session's held forms
//!
//! [`hovering`] parses the copy's text through its session's form store
//! without changing it. A document that imports a sibling is parsed as its
//! judgement parses it ([`Session::parse_held_unit`]): its own text alone,
//! through the forms the recheck before it molded, laid after the tree of the
//! closure whose lowering the process holds, so the closure is neither molded
//! nor looked up again; the closure is laid out by the dispatcher's
//! [`lay_out_shadowed`], which reads each sibling an editor holds as its copy
//! and every other once per process. The lowering and the typed run still
//! read the whole laid-out text, the closure with the document.
//!
//! The alternative was a whole parse of the laid-out text per revision: on
//! the λ-calculus closure of #776, half the table's time went to it. The
//! choice reverses with the one-tree component's: once each imported source
//! is composed once, the table reads the closure's typings where they are
//! kept and types the document's own declarations alone.
//!
//! # A hover answers the node under the cursor, never an ancestor
//!
//! A node the source wrote answers as itself: a pattern with its name and
//! the type its place in the scrutinee gives it, a constructor's name in a
//! pattern with the constructor's type, a loop's name where its cell declares
//! it with its path type. An answer from an enclosing node — the match for a
//! pattern inside it, the declaration for its loop — is a gap, not an answer:
//! a reader asking what `here` is learns nothing from the match's `?`.
//!
//! The editor's corpus sweep
//! (`editor::scenarios::sweeps::hovering_every_position_of_each_corpus_source_answers_without_fault`)
//! holds every node kind to that rule. It classes each position by the
//! smallest node holding it — a name a form spells as a node of its own, the
//! form's keywords and delimiters as the form's — and counts, per kind, the
//! positions answered at that node, by an ancestor, by nothing, with a `?`,
//! and in another shape than the kind's (below). Each count is pinned per kind
//! as an absolute ceiling, so deleting corpus text never fails the sweep; the
//! shares answered at the node and in shape are printed beside them and held
//! by none. A row moves only with a stated cause: a change that answers or
//! shapes a kind lowers it, a source added with misses raises it. The kinds
//! with no meaning of their own to hover are listed with why and counted but
//! not held: the parser's repair grout, which the source never wrote, and an
//! attribute's brackets, keywords, name and payload, which state what the
//! declaration they decorate is expected to do and are answered by it.
//!
//! The alternative was one corpus-wide answered share: it counts an answer
//! from the match as covering a pattern inside it, so a kind answered only by
//! its ancestors passed unseen. Shares per kind were the next alternative: a
//! source deleted can lower a share with every remaining position answered.
//! The table returns to one share if keeping its rows costs more than the
//! gaps they find.
//!
//! # A hover's content holds its node kind's shape
//!
//! Answering at the node says where the answer comes from, not what it says.
//! The guarantee comes in three layers:
//!
//! - **Coverage by node**: the sweep's counts above, per kind.
//! - **Content by shape and read-back**: each answer at its node holds the
//!   shape its kind demands — a name `<name> : <type>`, a written type `<type>
//!   : <universe>`, a literal its native type, a keyword or delimiter of a term
//!   the term's type, of a declaration the declaration's answer — with every
//!   type in it parsing as a written type; the sweep counts the answers out of
//!   shape per kind (`editor::shapes`). Every type the table prints is read
//!   back — parsed, lowered beside the source, compared with the certificate's
//!   type (`TypeTable::read_back`) — and the dispatcher's census pins the types
//!   that do not, by why. Five headline sources keep a golden of every hover
//!   beside their role goldens.
//! - **Totality, statically**: the `answer-totality` lint, queued — every path
//!   through the hover ends in an answer or a named absence.
//!
//! The alternative was a golden of every corpus hover: it pins everything
//! and no review can read it. Shapes hold the corpus; the goldens hold five
//! sources a reader checks line by line. The choice returns to goldens when
//! a generator over types draws the sources the goldens pin (issue #386).

use alloc::format;
use alloc::string::String;
use core::cell::OnceCell;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_dispatcher::Declared;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::Shadows;
use gandr_surface_dispatcher::Subject;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::TypedSpan;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out_shadowed;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Spelling;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::Session;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::complete::Names;
use crate::markup::Code;
use crate::markup::Host;
use crate::markup::Markup;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::Hover;
use crate::protocol::MarkupContent;
use crate::protocol::SymbolKind;
use crate::reading::Declaration;
use crate::reading::Reading;
use crate::reading::Written;
use crate::recheck::roles;
use crate::search::Found;
use crate::signature::Signatures;

/// The page width a hover lays a type out at.
const HOVER_WIDTH: u32 = 80;

quenchant_shape::reason_enum! {
    /// Why a position hovers nothing.
    pub mod hovered {
        /// The reason nothing is shown.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The grammar did not build or the text did not parse.
            Unparsed,
            /// The position is in no typed node and no declaration.
            Untyped,
        }
    }
}

/// What a document copy keeps for its hovers, its definitions, its
/// completions, its signature help and the workspace's symbols until its text
/// changes: the type table of its text, the path of each source of the unit
/// the table was typed in, the names the unit declares, the heads it declares
/// them with, and, once asked, where each name is written.
#[derive(Clone, Debug)]
pub struct Hovering
{
    /// The type of every node of the text, and of every declaration.
    table: TypeTable,
    /// The canonical path of each source of the table's unit, in the unit's
    /// order; empty for a text typed alone.
    paths: Vec<PathBuf>,
    /// The names the table's unit declares, by name.
    names: Names,
    /// The heads the table's unit declares, by where each name is written.
    signatures: Signatures,
    /// The names the table's unit declares with their ranges, made by the
    /// first workspace-symbol request.
    found: OnceCell<Found>,
}

impl Hovering
{
    /// The type table of the text.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn table(&self) -> &TypeTable
    {
        &self.table
    }

    /// The names the table's unit declares, by name.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn names(&self) -> &Names
    {
        &self.names
    }

    /// The heads the table's unit declares, by where each name is written.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn signatures(&self) -> &Signatures
    {
        &self.signatures
    }

    /// The canonical path of the unit's source `referent` stands in, none for
    /// a text typed alone.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn path(
        &self,
        referent: &Referent,
    ) -> Option<&Path>
    {
        self.paths
            .get(usize::from(referent.source()))
            .map(PathBuf::as_path)
    }

    /// The canonical path of the unit's source `source`, none for a text typed
    /// alone.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn source_path(
        &self,
        source: SourceIndex,
    ) -> Option<&Path>
    {
        self.paths.get(usize::from(source)).map(PathBuf::as_path)
    }

    /// The unit's source whose canonical path is `path`, none when the closure
    /// reads no such source or the text was typed alone.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first source of the closure whose path is `path`.
    /// - provides: where another document's name stands in this unit.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a walk over the closure's paths, one per source it reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling read by an importer and by itself is found
    ///   in each.
    /// - witness: `server::tests::references_find_a_name_s_uses_in_every_open_document`
    #[spec(ensures: |ret| ret.is_none_or(|source| self.source_path(source) == Some(path)))]
    pub(crate) fn source_at(
        &self,
        path: &Path,
    ) -> Option<SourceIndex>
    {
        self.paths
            .iter()
            .position(|held| held == path)
            .map(SourceIndex::from)
    }

    /// The names the table's unit declares, each with its name's range in its
    /// source's text, read at the first workspace-symbol request.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn found(&self) -> &Found
    {
        self.found.get_or_init(|| Found::of(&self.table))
    }
}

/// What the hovers of `text`, the document at `path` that `session` judges,
/// read: one typed run per text, rather than one per hover.
///
/// # Specification
/// - requires: nothing; `session` may have judged any revision.
/// - ensures: [`TypeTable::of_parsed_unit`] over the import closure the
///   dispatcher's [`lay_out_shadowed`] lays `text` out in under `shadows` when
///   it imports a sibling by path, parsed as `session`'s judgement parses it
///   ([`Session::parse_held_unit`]), beside the closure's paths, else
///   [`TypeTable::of_parsed`] over `text` parsed through `session`'s form store
///   ([`Session::parse_held`]), beside no path; the store is left as it was,
///   and the table is empty when the text did not parse.
/// - provides: what a document copy keeps for its hovers, its definitions, its
///   completions and its signature help: the names read off the table once
///   ([`Names::of`]) and the heads read off the same parse
///   ([`Signatures::of`]); a name an import brings in types at its use as its
///   declaration does.
/// - fails: never; a refusal answers the empty table.
/// - panics: none.
/// - executable: none — the table is the dispatcher's typed run, whose own
///   specification states what it holds; restating it here would run the typed
///   run again.
///
/// # Adequacy
/// - hypothesis: L3 — a hover over every kind of position reads what this
///   builds, so a table of another text, or an empty one, changes a typed
///   answer; a hover on an imported name in a corpus importer answers its type.
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::an_imported_name_hovers_its_declaration_s_type`
#[must_use]
pub fn hovering<Store, Blocks>(
    text: SourceText<'_>,
    path: &Path,
    session: &Session<Store, Blocks>,
    shadows: &dyn Shadows,
) -> Hovering
{
    let grammar = session.grammar();
    let heads = |tree: &SyntaxTree<'_>, unit: &Unit| {
        roles().map_or_else(
            |_| Signatures::default(),
            |roles| Signatures::of(grammar, roles, tree, unit),
        )
    };
    let (typed, paths) = match lay_out_shadowed(grammar, path, classify(path), text, shadows) {
        Maybe::Present(laid) => (
            session
                .parse_held_unit(SourceText::from(laid.text.as_str()), &laid.unit, laid.base)
                .ok()
                .and_then(|parsed| {
                    let signatures = heads(parsed.tree(), &laid.unit);
                    TypeTable::of_parsed_unit(grammar, parsed, &laid.unit, laid.base)
                        .ok()
                        .map(|table| (table, signatures))
                }),
            laid.paths,
        ),
        Maybe::Absent(_) => (
            session.parse_held(text).ok().and_then(|parsed| {
                let signatures = heads(parsed.tree(), &Unit::single());
                TypeTable::of_parsed(grammar, parsed)
                    .ok()
                    .map(|table| (table, signatures))
            }),
            Vec::new(),
        ),
    };
    let (table, signatures) = typed.unwrap_or_default();
    Hovering {
        names: Names::of(&table),
        table,
        paths,
        signatures,
        found: OnceCell::new(),
    }
}

/// How a hover spells and writes what it shows: the presentation form and
/// spelling of its types and the markup its client renders.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Style
{
    /// The form every type is spelled in.
    pub form: Form,
    /// The spelling every type is written in.
    pub spelling: Spelling,
    /// The markup the hover is written in.
    pub markup: Markup,
}

impl Style
{
    /// The printer's style of these: the form and the spelling.
    ///
    /// # Specification
    /// trivial.
    pub const fn printed(self) -> gandr_surface_pretty::Style
    {
        gandr_surface_pretty::Style {
            form: self.form,
            spelling: self.spelling,
        }
    }
}

/// What a hover at `position` of `text` shows, read against the text's
/// `reading`, its `hovering` and `session`, in `style`.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`, and `session`
///   last checked `text`, as the server's synchronisation leaves them; a stale
///   session answers the documentation it last accepted.
/// - ensures: on a declaration's name — from its first character to just past
///   its last — [`declared`]'s block about the name's range: the name and its
///   type when the table types it, the name and the lowering's refusal when the
///   table holds one, else the declaration as written, a theory and a module
///   always so; then the documentation the session filed for the form after a
///   blank line. On a member's name with no entry inside the member, the member
///   as written, about the name. Else, in a run a theory writes that declares
///   nothing, with no entry inside it, the run as written, about it. Else, on
///   the innermost typed node holding the position: inside a member whose
///   entries are none of them there, the member as written, about the member;
///   when the node spans a whole declaration — its body's term written over the
///   declaration, or a module's instantiation written over the module (#405) —
///   as on that declaration's name, about its head when the position is there
///   and the node's range otherwise; else a block of its type — a binder's
///   name, a written type's text or a term written as one name before ` : ` —
///   and, for a term checked against a type spelled otherwise, that type in a
///   second block, about the node's range. Else, in the head of a declaration —
///   from its form's start to the brace opening its own body, a member's
///   keyword to its name — as on its name, about the head, and in the
///   attributes before the head, about them. Absent elsewhere. Every type is
///   spelled in `style`'s form, and every block is written as [`Code`] writes
///   it in `style`'s markup.
/// - provides: the answer to `textDocument/hover`.
/// - fails: never; an absence names its reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a documented definition, an undocumented one, a member of
///   a module sharing its name with another module's, a signature and its
///   definition, a function and one the lowering refused, a binder, a use,
///   written value and computation types, a mismatched term, a term past a
///   refusal in its body, a keyword, layout inside a declaration, a word in a
///   comment and a position past the last declaration are asserted at their
///   exact answers, and so is each position a fixed defect hovered wrongly — a
///   decode and a constructor written in a type, a type under a static binder,
///   a module's instantiation and two pattern tiles; a theory, its `include`, a
///   module's name and ascription, a type alias, a shape and a circuit rule as
///   written; a declaration and a written type in HTML, coloured by their
///   roles.
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::each_member_hovers_its_own_type`
/// - witness: `hover::tests::html_hovers_colour_the_name_and_the_type`
/// - witness: `hover::tests::a_decode_written_as_a_type_hovers_as_a_type_419`
/// - witness: `hover::tests::a_constructor_applied_inside_a_type_hovers_its_text_420`
/// - witness: `hover::tests::a_type_under_a_static_binder_hovers_its_text_404`
/// - witness: `hover::tests::a_module_instantiation_answers_itself_never_a_member_s_type_405`
/// - witness: `hover::tests::a_theory_and_a_module_hover_as_written_1122_1124`
/// - witness: `hover::tests::the_parentheses_around_an_inverted_letter_answer_the_cons_pattern_408`
/// - witness: `hover::tests::a_sum_pattern_s_positional_label_answers_as_a_label_408`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref hover) => hover.contents.value.starts_with(style.markup.opener().0)
        && hover.range.start <= position && position <= hover.range.end,
    Maybe::Absent(_) => true,
})]
pub fn hover<Store, Blocks>(
    text: SourceText<'_>,
    session: &Session<Store, Blocks>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    style: Style,
) -> Maybe<Hover, hovered::Absent>
{
    let Maybe::Present(found) = reading.declarations()
    else {
        return Maybe::Absent(hovered::Absent::Unparsed);
    };
    let table = &hovering.table;
    let index = LineIndex::new(<&str>::from(text).into());
    let quoted = Quoted {
        text,
        index: &index,
        spans: reading.spans(),
    };
    let offset = ByteOffset::from(usize::from(position.byte(&index)));
    let entry = table.at(offset, PageWidth::from(HOVER_WIDTH), style.printed());
    let entered = match entry {
        Maybe::Present(ref entry) => Some((
            usize::from(entry.span().start()),
            usize::from(entry.span().end()),
        )),
        Maybe::Absent(_) => None,
    };
    // A member written among its holder's tiles has no form of its own to key
    // a type or documentation by: the table types it where an entry inside it
    // answers, and it answers as written where the only entry is its
    // holder's.
    let typed_inside = |member: &Declaration| {
        let start = usize::from(member.symbol.range.start.byte(&index));
        let end = usize::from(member.symbol.range.end.byte(&index));
        entered.is_some_and(|(from, to)| start <= from && to <= end)
    };
    let forms = || found.iter().filter(|found| found.written == Written::Form);
    if let Some(named) = found.iter().find(|found| {
        found.symbol.selection_range.start <= position
            && position <= found.symbol.selection_range.end
    }) {
        match named.written {
            Written::Form => {
                return Maybe::Present(declared(
                    session,
                    table,
                    named,
                    named.symbol.selection_range,
                    &quoted,
                    style,
                ));
            },
            Written::Member if !typed_inside(named) => {
                return Maybe::Present(member(named, named.symbol.selection_range, &quoted, style));
            },
            Written::Member => {},
        }
    }
    // A run a theory writes that declares nothing — an `include` — answers as
    // written where nothing inside it is typed.
    let at = usize::from(offset);
    let unnamed = forms()
        .flat_map(|form| form.members.iter())
        .map(|run| (usize::from(run.start()), usize::from(run.end())))
        .find(|&(start, end)| {
            start <= at
                && at < end
                && !entered.is_some_and(|(from, to)| start <= from && to <= end)
                && !found.iter().any(|found| {
                    found.written == Written::Member
                        && usize::from(found.symbol.range.start.byte(&index)) == start
                })
        });
    if let Some((start, end)) = unnamed
        && let Ok(range) =
            Range::of_bytes(&index, RenderOffset::from(start), RenderOffset::from(end))
    {
        return Maybe::Present(as_written(
            RenderOffset::from(start),
            RenderOffset::from(end),
            range,
            &quoted,
            style,
        ));
    }
    let oriented = table
        .orientations()
        .iter()
        .find_map(|&(span, note)| (span.start() <= offset && offset < span.end()).then_some(note));
    if let Maybe::Present(entry) = entry
        && let Ok(range) = Range::of_bytes(
            &index,
            RenderOffset::from(usize::from(entry.span().start())),
            RenderOffset::from(usize::from(entry.span().end())),
        )
    {
        if let Some(held) = found.iter().rfind(|found| {
            found.written == Written::Member
                && found.symbol.range.start <= position
                && position <= found.symbol.range.end
                && !typed_inside(found)
        }) {
            return Maybe::Present(member(held, held.symbol.range, &quoted, style));
        }
        // An entry standing for a whole declaration — its body's term, or a
        // module's instantiation, written at the declaration's span — answers
        // as the declaration it stands for. A module with a body has no entry
        // over it whole, so its members answer for themselves; an
        // instantiation's entry is one of the members it instantiates, so a
        // module answers itself, never a member's type (#405).
        if let Some(whole) = forms().rfind(|found| {
            range.start <= found.symbol.selection_range.start
                && found.symbol.range.end <= range.end
                && found.symbol.range.start <= position
                && position <= found.symbol.range.end
        }) {
            let about = if whole.head.start <= position && position < whole.head.end {
                whole.head
            }
            else {
                range
            };
            return Maybe::Present(declared(session, table, whole, about, &quoted, style));
        }
        let mut value = typed(&quoted, &entry, style.markup);
        if let Some(note) = oriented {
            value.push_str("\n\n");
            value.push_str(match note {
                gandr_surface_dispatcher::ChosenDirection::LeftToRight => "oriented left to right",
                gandr_surface_dispatcher::ChosenDirection::RightToLeft => "oriented right to left",
            });
        }
        return Maybe::Present(Hover {
            contents: MarkupContent {
                kind: "markdown",
                value,
            },
            range,
        });
    }
    if let Some(note) = oriented {
        let found = table
            .orientations()
            .iter()
            .find(|&&(span, _)| span.start() <= offset && offset < span.end());
        if let Some(&(span, _)) = found
            && let Ok(range) = Range::of_bytes(
                &index,
                RenderOffset::from(usize::from(span.start())),
                RenderOffset::from(usize::from(span.end())),
            )
        {
            let mut code = Code::new(style.markup);
            code.plain(SourceText::from(match note {
                gandr_surface_dispatcher::ChosenDirection::LeftToRight => "oriented left to right",
                gandr_surface_dispatcher::ChosenDirection::RightToLeft => "oriented right to left",
            }));
            return Maybe::Present(Hover {
                contents: MarkupContent {
                    kind: "markdown",
                    value: code.block(),
                },
                range,
            });
        }
    }
    // The head answers its declaration — a module's ascription and a member's
    // keyword included — and so do the attributes before it, about their own
    // stretch.
    let enclosing = found
        .iter()
        .rfind(|found| found.symbol.range.start <= position && position < found.head.end);
    enclosing.map_or(Maybe::Absent(hovered::Absent::Untyped), |enclosing| {
        let about = if enclosing.head.start <= position {
            enclosing.head
        }
        else {
            Range {
                start: enclosing.symbol.range.start,
                end: enclosing.head.start,
            }
        };
        Maybe::Present(match enclosing.written {
            Written::Form => declared(session, table, enclosing, about, &quoted, style),
            Written::Member => member(enclosing, about, &quoted, style),
        })
    })
}

/// The document a hover quotes from: its text, its line index and the
/// highlighter's spans over it.
#[derive(Clone, Copy, Debug)]
struct Quoted<'text>
{
    /// The document's text.
    text: SourceText<'text>,
    /// The line index of `text`.
    index: &'text LineIndex<'text>,
    /// The highlighter's spans over `text`, sorted and disjoint.
    spans: &'text [HlSpan],
}

impl Quoted<'_>
{
    /// Append to `code` the document's text over `bytes` when it is `quoted`,
    /// in the colours the document gives it; else `quoted` uncoloured.
    ///
    /// # Specification
    /// trivial.
    fn quote(
        &self,
        code: &mut Code,
        quoted: SourceText<'_>,
        start: RenderOffset,
    )
    {
        let from = usize::from(start);
        let text = <&str>::from(quoted);
        let written = <&str>::from(self.text).get(from .. from.saturating_add(text.len()));
        if written == Some(text) {
            code.quoted(quoted, start, self.spans);
        }
        else {
            code.plain(quoted);
        }
    }
}

/// The hover of the declaration `declaration`, about `range`.
///
/// # Specification
/// - requires: `range` holds the hovered position, and `quoted` is the document
///   `declaration` was read from.
/// - ensures: a block of the declaration. For one that is neither a module nor
///   a theory and that `table` types by its form's key: the name — in the
///   colours the document gives it — then ` : ` and its type in `style`'s form.
///   For one `table` holds the lowering's refusal of instead: the name, then
///   that refusal after a blank line. Otherwise, a theory and a module always
///   among them, the declaration as [`written`] writes it, a theory with its
///   members. Then the documentation `session` filed under the form's key after
///   a blank line.
/// - provides: the declaration half of [`hover`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`hover`]'s declaration rows.
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
/// - witness: `hover::tests::each_member_hovers_its_own_type`
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::html_hovers_colour_the_name_and_the_type`
/// - witness: `hover::tests::a_theory_and_a_module_hover_as_written_1122_1124`
#[spec(ensures: |ref ret| ret.range == range
    && ret.contents.value.starts_with(style.markup.opener().0))]
fn declared<Store, Blocks>(
    session: &Session<Store, Blocks>,
    table: &TypeTable,
    declaration: &Declaration,
    range: Range,
    quoted: &Quoted<'_>,
    style: Style,
) -> Hover
{
    let symbol = &declaration.symbol;
    let key = declaration.key;
    let theory = symbol.kind == SymbolKind::INTERFACE;
    let held = key
        .filter(|_| symbol.kind != SymbolKind::MODULE)
        .and_then(
            |key| match table.declared(key, PageWidth::from(HOVER_WIDTH), style.printed()) {
                Maybe::Present(held) => Some(held),
                Maybe::Absent(_) => None,
            },
        );
    let documented = key.and_then(|key| match session.documentation(key) {
        Maybe::Present(text) => Some(text),
        Maybe::Absent(_) => None,
    });
    let mut code = Code::new(style.markup);
    let name = |code: &mut Code| {
        let start = symbol.selection_range.start.byte(quoted.index);
        quoted.quote(code, SourceText::from(symbol.name.as_str()), start);
    };
    let mut value = match held {
        Some(Declared::Typed(spelled)) if !theory => {
            name(&mut code);
            code.printed(
                SourceText::from(format!(" : {}", spelled.as_ref()).as_str()),
                Host::Signature,
            );
            code.block()
        },
        Some(Declared::Refused(refusal)) => {
            if theory {
                written(&mut code, declaration, quoted);
            }
            else {
                name(&mut code);
            }
            format!("{}\n\nrefused: {refusal}", code.block())
        },
        Some(Declared::Typed(_)) | None => {
            written(&mut code, declaration, quoted);
            code.block()
        },
    };
    if let Some(text) = documented {
        value.push_str("\n\n");
        value.push_str(text.as_ref());
    }
    Hover {
        contents: MarkupContent {
            kind: "markdown",
            value,
        },
        range,
    }
}

/// The hover of `member`, a member its holder writes among its own tiles,
/// about `range`.
///
/// # Specification
/// - requires: `range` holds the hovered position, and `quoted` is the document
///   `member` was read from.
/// - ensures: [`as_written`] over the member's range, the body an operation or
///   a rule fills — from its first `{` — left out.
/// - provides: the member half of [`hover`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a shape with its faces, a circuit rule with a body, and a
///   member's keyword are asserted at their exact answers.
/// - witness: `hover::tests::a_theory_and_a_module_hover_as_written_1122_1124`
/// - witness: `hover::tests::a_described_member_hovers_its_own_type`
#[spec(ensures: |ref ret| ret.range == range
    && ret.contents.value.starts_with(style.markup.opener().0))]
fn member(
    member: &Declaration,
    range: Range,
    quoted: &Quoted<'_>,
    style: Style,
) -> Hover
{
    let start = member.symbol.range.start.byte(quoted.index);
    let end = member.symbol.range.end.byte(quoted.index);
    let open = <&str>::from(quoted.text)
        .get(usize::from(start) .. usize::from(end))
        .and_then(|run| run.find('{'))
        .filter(|_| {
            matches!(
                member.symbol.kind,
                SymbolKind::METHOD | SymbolKind::PROPERTY
            )
        });
    let end = open.map_or(end, |open| {
        RenderOffset::from(usize::from(start).saturating_add(open))
    });
    as_written(start, end, range, quoted, style)
}

/// The hover of the document's text from byte `start` to byte `end`, about
/// `range`.
///
/// # Specification
/// - requires: `range` holds the hovered position, and `start` and `end` fall
///   on character boundaries of `quoted`'s text.
/// - ensures: a block of the text as the document writes it, in its colours,
///   each line after the first taken back to the indentation of the line it
///   starts on, without trailing layout or a trailing `;`.
/// - provides: the hover of a member, and of a run a theory writes that
///   declares nothing, as an `include`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`member`], and an `include` hovers as written.
/// - witness: `hover::tests::a_theory_and_a_module_hover_as_written_1122_1124`
#[spec(ensures: |ref ret| ret.range == range
    && ret.contents.value.starts_with(style.markup.opener().0))]
fn as_written(
    start: RenderOffset,
    end: RenderOffset,
    range: Range,
    quoted: &Quoted<'_>,
    style: Style,
) -> Hover
{
    let run = <&str>::from(quoted.text)
        .get(usize::from(start) .. usize::from(end))
        .unwrap_or_default();
    let mut code = Code::new(style.markup);
    lines(
        &mut code,
        quoted,
        start,
        SourceText::from(run.trim_end().trim_end_matches(';').trim_end()),
        SourceText::from(""),
    );
    Hover {
        contents: MarkupContent {
            kind: "markdown",
            value: code.block(),
        },
        range,
    }
}

/// Append to `code` the declaration `declaration` as the document writes it,
/// in its colours: its head — from its form's own start to the brace opening
/// its own body, or its whole text without a trailing `;` for a form without
/// one — and, for a theory, its members between braces, one to a line
/// indented by two spaces, an `include` among them as written.
///
/// # Specification
/// trivial.
fn written(
    code: &mut Code,
    declaration: &Declaration,
    quoted: &Quoted<'_>,
)
{
    let text = <&str>::from(quoted.text);
    let start = usize::from(declaration.head.start.byte(quoted.index));
    let end = usize::from(declaration.head.end.byte(quoted.index));
    let head = text.get(start .. end).unwrap_or_default();
    lines(
        code,
        quoted,
        RenderOffset::from(start),
        SourceText::from(head.trim_end().trim_end_matches(';').trim_end()),
        SourceText::from(""),
    );
    if declaration.symbol.kind != SymbolKind::INTERFACE {
        return;
    }
    code.plain(SourceText::from(" {"));
    for &run in &declaration.members {
        let from = usize::from(run.start());
        let written = text.get(from .. usize::from(run.end())).unwrap_or_default();
        code.plain(SourceText::from("\n  "));
        lines(
            code,
            quoted,
            RenderOffset::from(from),
            SourceText::from(written.trim_end()),
            SourceText::from("  "),
        );
    }
    code.plain(SourceText::from("\n}"));
}

/// Append to `code` `run`, the document's text from byte `start`, a line at
/// a time in the document's colours: each line after the first with as much
/// of the indentation of the line `run` starts on taken off as it has, and
/// `indent` before it.
///
/// # Specification
/// trivial.
fn lines(
    code: &mut Code,
    quoted: &Quoted<'_>,
    start: RenderOffset,
    run: SourceText<'_>,
    indent: SourceText<'_>,
)
{
    let text = <&str>::from(quoted.text);
    let start = usize::from(start);
    let column = text
        .get(.. start)
        .and_then(|before| before.rfind('\n'))
        .map_or(start, |newline| {
            start.saturating_sub(newline).saturating_sub(1)
        });
    let mut at = start;
    for (number, line) in <&str>::from(run).split('\n').enumerate() {
        let cut = if number == 0 {
            0
        }
        else {
            code.plain(SourceText::from("\n"));
            code.plain(indent);
            line.len()
                .saturating_sub(line.trim_start_matches(' ').len())
                .min(column)
        };
        quoted.quote(
            code,
            SourceText::from(line.get(cut ..).unwrap_or_default()),
            RenderOffset::from(at.saturating_add(cut)),
        );
        at = at.saturating_add(line.len()).saturating_add(1);
    }
}

/// The hover text of the typed node `entry` of the `quoted` document, in
/// `markup`.
///
/// # Specification
/// - requires: `entry` was read from the table of the `quoted` document.
/// - ensures: a block: a binder's name, a written type's text, a term the
///   document writes as one name — one highlighter span over exactly the term,
///   in a name's role: a variable, a parameter, a function, a member, a
///   constructor, a type, a type variable or a label, never a literal, a
///   keyword or an operator — and a constructor applied to its arguments — a
///   term whose first highlighter span starts it in a constructor's role, or a
///   type's where a type's argument writes it — each when it is one line of the
///   source and in the colours the document gives it, then ` : ` and the
///   entry's type; any other term's type alone; for a term checked against a
///   type spelled otherwise, a second block of that type after a line saying
///   so.
/// - provides: the node half of [`hover`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a use, a binder, a written type, a literal and a
///   mismatched term are asserted at their exact texts.
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::html_hovers_colour_the_name_and_the_type`
#[spec(ensures: |ret| ret.starts_with(markup.opener().0))]
fn typed(
    quoted: &Quoted<'_>,
    entry: &TypedSpan,
    markup: Markup,
) -> String
{
    let start = usize::from(entry.span().start());
    let end = usize::from(entry.span().end());
    let at = quoted
        .spans
        .partition_point(|span| usize::from(span.range.start()) < start);
    let first = quoted
        .spans
        .get(at)
        .filter(|span| usize::from(span.range.start()) == start);
    let named = || {
        first.is_some_and(|span| {
            usize::from(span.range.end()) == end
                && matches!(
                    span.role,
                    HlRole::FunctionDef
                        | HlRole::FunctionCall
                        | HlRole::VariableDef
                        | HlRole::VariableParam
                        | HlRole::Member
                        | HlRole::Variable
                        | HlRole::Constructor
                        | HlRole::Type
                        | HlRole::TypeBuiltin
                        | HlRole::TypeVariable
                        | HlRole::Label
                )
        })
    };
    let constructed =
        || first.is_some_and(|span| matches!(span.role, HlRole::Constructor | HlRole::Type));
    let written = <&str>::from(quoted.text)
        .get(start .. end)
        .filter(|written| !written.contains('\n'))
        .filter(|_| match entry.subject() {
            Subject::Binder | Subject::Type => true,
            Subject::Term => named() || constructed(),
        });
    let mut code = Code::new(markup);
    match written {
        Some(written) => {
            quoted.quote(
                &mut code,
                SourceText::from(written),
                RenderOffset::from(start),
            );
            code.printed(
                SourceText::from(format!(" : {}", entry.ty().as_ref()).as_str()),
                Host::Signature,
            );
        },
        None => {
            code.printed(SourceText::from(entry.ty().as_ref()), Host::Type);
        },
    }
    let mut value = code.block();
    if let Maybe::Present(expected) = entry.expected() {
        let mut against = Code::new(markup);
        against.printed(SourceText::from(expected.as_ref()), Host::Type);
        value.push_str("\n\nchecked against\n\n");
        value.push_str(&against.block());
    }
    value
}

#[cfg(test)]
mod tests
{
    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_pretty::Form;
    use gandr_surface_pretty::Spelling;
    use gandr_surface_render_remote::ByteOffset as RenderOffset;
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_session::Session;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Style;
    use super::hover;
    use super::hovered;
    use super::hovering;
    use crate::markup::Markup;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::reading::Reading;
    use crate::recheck::grammar;

    /// The style a client keeping no HTML tags reads, in the explicit form
    /// the fixtures below are written in.
    const PLAIN: Style = Style {
        form: Form::Explicit,
        spelling: Spelling::Unicode,
        markup: Markup::Markdown,
    };

    /// A session that has checked `text`.
    ///
    /// # Specification
    /// trivial.
    fn checked(text: SourceText<'_>) -> Session<MemoryCheckpointStore, InMemoryBlockStore>
    {
        let mut session = Session::new(
            grammar().expect("the grammar builds").clone(),
            SourceRoot::Strict,
            MemoryCheckpointStore::default(),
            InMemoryBlockStore::default(),
            BackendArtifact::from(b"hover".as_slice()),
        );
        let _judged = session.judge(text).expect("the session does not fault");
        session
    }

    /// What a hover at `line` and `character` of `text` shows, or why not.
    ///
    /// # Specification
    /// trivial.
    fn shown(
        text: SourceText<'_>,
        (line, character): (Line, Character),
    ) -> Result<String, hovered::Absent>
    {
        shown_at(text, Position { line, character })
    }

    /// What a hover at `position` of `text` shows in markdown and the
    /// explicit form, or why not.
    ///
    /// # Specification
    /// trivial.
    fn shown_at(
        text: SourceText<'_>,
        position: Position,
    ) -> Result<String, hovered::Absent>
    {
        styled(text, position, PLAIN)
    }

    /// What a hover at `position` of `text` shows in `style`, or why not.
    ///
    /// # Specification
    /// trivial.
    fn styled(
        text: SourceText<'_>,
        position: Position,
        style: Style,
    ) -> Result<String, hovered::Absent>
    {
        let session = checked(text);
        match hover(
            text,
            &session,
            &Reading::of(text),
            &hovering(
                text,
                std::path::Path::new(""),
                &session,
                &gandr_surface_dispatcher::Unshadowed,
            ),
            position,
            style,
        ) {
            Maybe::Present(shown) => Ok(shown.contents.value),
            Maybe::Absent(reason) => Err(reason),
        }
    }

    /// The marker `$0`'s position in `fixture`, and the fixture without it;
    /// panics when the marker is missing.
    ///
    /// # Specification
    /// trivial.
    fn marker(fixture: SourceText<'_>) -> (String, Position)
    {
        let written = <&str>::from(fixture);
        let at = written.find("$0").expect("the fixture is marked");
        let text = written.replacen("$0", "", 1);
        let index = LineIndex::new(text.as_str().into());
        let position =
            Position::of_byte(&index, RenderOffset::from(at)).expect("the marker is on a boundary");
        (text, position)
    }

    /// A hover's text: one fenced block holding `block`.
    ///
    /// # Specification
    /// trivial.
    fn fenced(block: SourceText<'_>) -> String
    {
        format!("```gandr\n{}\n```", <&str>::from(block))
    }

    #[test]
    fn an_imported_name_hovers_its_declaration_s_type()
    {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus/fixture/model/identity/circle-elim.gandr");
        let written = std::fs::read_to_string(&path).expect("the corpus importer is read");
        let text = SourceText::from(written.as_str());
        let at = written
            .find("Circle) -> -F Path")
            .expect("a parameter's type names the circle");
        let index = LineIndex::new(written.as_str().into());
        let position =
            Position::of_byte(&index, RenderOffset::from(at)).expect("the name is on a boundary");
        let session = checked(text);
        let shown = hover(
            text,
            &session,
            &Reading::of(text),
            &hovering(text, &path, &session, &gandr_surface_dispatcher::Unshadowed),
            position,
            PLAIN,
        );
        assert_eq!(
            match shown {
                Maybe::Present(shown) => Ok(shown.contents.value),
                Maybe::Absent(reason) => Err(reason),
            },
            Ok(fenced(SourceText::from("Circle : Type"))),
            "`Circle`, which `circle-base.gandr` declares, answers as its own source's type"
        );
    }

    /// Hovering a declaration's name and hovering its written type print the
    /// type in one form: the sugared default writes the composite the
    /// transport derives as `then`, as the source does.
    #[test]
    fn a_declaration_s_name_and_its_written_type_print_one_form_754()
    {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus/fixture/model/identity/circle.gandr");
        let written = std::fs::read_to_string(&path).expect("the corpus source is read");
        let text = SourceText::from(written.as_str());
        let line = written
            .find("def twice : Path(")
            .expect("the source declares `twice`");
        let index = LineIndex::new(written.as_str().into());
        let session = checked(text);
        let reading = Reading::of(text);
        let hovering = hovering(text, &path, &session, &gandr_surface_dispatcher::Unshadowed);
        let sugared = Style {
            form: Form::Sugared,
            spelling: Spelling::Unicode,
            markup: Markup::Markdown,
        };
        let at = |offset: usize| {
            let position = Position::of_byte(&index, RenderOffset::from(offset))
                .expect("the offset is on a boundary");
            match hover(text, &session, &reading, &hovering, position, sugared) {
                Maybe::Present(shown) => shown.contents.value,
                Maybe::Absent(reason) => panic!("the position hovers nothing: {reason:?}"),
            }
        };
        let ty = "Path(Path(Circle, Base, Base), loop then loop, loop ∷ loop ∷ here(Base))";
        let named = at(line.saturating_add("def tw".len()));
        assert!(
            named.starts_with(&fenced(SourceText::from(format!("twice : {ty}").as_str()))),
            "the name prints the type as written: {named}"
        );
        assert_eq!(
            at(line.saturating_add("def twice : Pa".len())),
            fenced(SourceText::from(format!("{ty} : Type").as_str())),
            "the written type prints the same text"
        );
    }

    #[test]
    fn each_marked_position_hovers_its_answer()
    {
        let rows: [(&str, &str, Result<String, hovered::Absent>); 19] = [
            (
                "a synthesised declaration's name",
                "def ans$0wer = 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "the definition half of a signed declaration",
                "def answer : Integer ;\ndef ans$0wer = 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "a function's name",
                "def $0f(x: Integer) -> -F Integer { return x }\n",
                Ok(fenced(SourceText::from("f : +U (Integer -> -F Integer)"))),
            ),
            (
                "the name of a function the lowering refused",
                "def $0f(x: Integer) -> -F Integer { run y <- return x ; return y }\n",
                Ok(String::from(
                    "```gandr\nf\n```\n\nrefused: no path reaches this code: every path \
                     through the statement before it exits",
                )),
            ),
            (
                "a binder",
                "def f($0x: Integer) -> -F Integer { return x }\n",
                Ok(fenced(SourceText::from("x : Integer"))),
            ),
            (
                "a use",
                "def f(x: Integer) -> -F Integer { return $0x }\n",
                Ok(fenced(SourceText::from("x : Integer"))),
            ),
            (
                "a literal",
                "def f(x: Integer) -> -F Integer { return 4$02 }\n",
                Ok(fenced(SourceText::from("Integer"))),
            ),
            (
                "the keyword introducing a function",
                "d$0ef f(x: Integer) -> -F Integer { return x }\n",
                Ok(fenced(SourceText::from("f : +U (Integer -> -F Integer)"))),
            ),
            (
                "the brace closing a function's body",
                "def f(x: Integer) -> -F Integer { return x $0}\n",
                Ok(fenced(SourceText::from("f : +U (Integer -> -F Integer)"))),
            ),
            (
                "a written value type",
                "def answer : Inte$0ger ;\n",
                Ok(fenced(SourceText::from("Integer : Type"))),
            ),
            (
                "a declaration written with a dependent record",
                "def r$0ing : #{n : Integer, v : Path(Integer, n, n)} ;\ndef ring = #{2, here(2)} \
                 ;\n",
                Ok(fenced(SourceText::from(
                    "ring : #{a : Integer, b : Path(Integer, a, a)}",
                ))),
            ),
            (
                "a written computation type",
                "def f(x: Integer) -> -$0F Integer { return x }\n",
                Ok(fenced(SourceText::from("-F Integer : Type[-]"))),
            ),
            (
                "a keyword opening a term",
                "def f(x: Integer) -> -F Integer { ret$0urn x }\n",
                Ok(fenced(SourceText::from("-F Integer"))),
            ),
            (
                "the keyword introducing a declaration",
                "d$0ef answer = 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "layout inside a declaration",
                "def answer =$0 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "a mismatched term",
                "def bad : Integer ;\ndef bad = u$0nit ;\n",
                Ok(String::from(
                    "```gandr\nUnit\n```\n\nchecked against\n\n```gandr\nInteger\n```",
                )),
            ),
            (
                "a term past a refusal in its body",
                "def g(x: Integer) -> -F Integer { run y <- force 1 ; return $0x }\n",
                Ok(fenced(SourceText::from("x : Integer"))),
            ),
            (
                "a comment between declarations",
                "def a = 1 ;\n// a $0word\ndef b = 2 ;\n",
                Err(hovered::Absent::Untyped),
            ),
            (
                "past the last declaration",
                "def later : Integer ;\n$0",
                Err(hovered::Absent::Untyped),
            ),
        ];
        for (position, fixture, expected) in rows {
            assert_eq!(marked(SourceText::from(fixture)), expected, "{position}");
        }
    }

    /// The hover at the marker `$0` in `fixture`.
    ///
    /// # Specification
    /// trivial.
    fn marked(fixture: SourceText<'_>) -> Result<String, hovered::Absent>
    {
        let (text, at) = marker(fixture);
        shown_at(SourceText::from(text.as_str()), at)
    }

    #[test]
    fn a_decode_written_as_a_type_hovers_as_a_type_419()
    {
        assert_eq!(
            marked(SourceText::from(
                "data Flag : Type {\n  On : Flag;\n  Off : Flag;\n}\ndef decoded(f : Flag) -> -F \
                 Type { case f { On => return Integer, Off => return Unit } }\ndef kept(f : \
                 Flag, n : decoded$0(f)) -> -F decoded(f) { return n }\n"
            )),
            Ok(fenced(SourceText::from("decoded(f) : Type")))
        );
    }

    #[test]
    fn a_constructor_applied_inside_a_type_hovers_its_text_420()
    {
        assert_eq!(
            marked(SourceText::from(
                "data U : Type {\n  NatC : U;\n  Arrow : (a : U, b : U) --> U;\n}\ndef el(u : U) \
                 -> -F Type { case u { NatC => return Integer, Arrow(a, b) => return Unit } \
                 }\ndef k : el(Arrow$0(NatC, NatC)) ;\n"
            )),
            Ok(fenced(SourceText::from("Arrow(NatC, NatC) : U")))
        );
    }

    #[test]
    fn a_type_under_a_static_binder_hovers_its_text_404()
    {
        assert_eq!(
            marked(SourceText::from(
                "def pair : Type -> Type[-] ;\ndef pair = \\X. -$0F (X * X) ;\n"
            )),
            Ok(fenced(SourceText::from("-F (X * X) : Type[-]")))
        );
    }

    #[test]
    fn a_module_instantiation_answers_itself_never_a_member_s_type_405()
    {
        assert_eq!(
            marked(SourceText::from(
                "module Seed :> #{ type T, zero : T } {\n  type T = Integer;\n  def zero = \
                 0;\n}\nmodule Keep(S : #{ type T, zero : T }) :> #{ type T, zero : T } {\n  type \
                 T = S.T;\n  def zero = S.zero;\n}\nmodule A = Keep(S$0eed) ;\n"
            )),
            Ok(fenced(SourceText::from("module A = Keep(Seed)")))
        );
    }

    #[test]
    fn the_parentheses_around_an_inverted_letter_answer_the_cons_pattern_408()
    {
        assert_eq!(
            marked(SourceText::from(
                "data Circle : Type { Base : Circle; loop : Base <-> Base; }\ndef rec size(p : \
                 Path(Circle, Base, Base)) -> -F Integer {\n  case p {\n    here => return 0,\n    \
                 loop ∷ q => become size[<](q),\n    back$0(loop) ∷ q => become size[<](q)\n  }\n}\n"
            )),
            Ok(fenced(SourceText::from(
                "back(loop) ∷ q : Path(Circle, Base, Base)"
            )))
        );
    }

    #[test]
    fn a_sum_pattern_s_positional_label_answers_as_a_label_408()
    {
        assert_eq!(
            marked(SourceText::from(
                "def flip(b : +{Unit, Unit}) -> -F +{Unit, Unit} {\n  case b {\n    +{.$00 = u} => \
                 return +{.1 = u},\n    +{.1 = u} => return +{.0 = u}\n  }\n}\n"
            )),
            Ok(fenced(SourceText::from("0 : Unit")))
        );
    }

    #[test]
    fn a_declaration_hovers_its_type_and_documentation()
    {
        let text = SourceText::from(
            "/// The answer, said once.\ndef answer = 42 ;\ndef plain : String ;\n",
        );
        assert_eq!(
            shown(text, (1.into(), 5.into())),
            Ok(String::from(
                "```gandr\nanswer : Integer\n```\n\nThe answer, said once."
            ))
        );
        assert_eq!(
            shown(text, (2.into(), 4.into())),
            Ok(String::from("```gandr\nplain : String\n```"))
        );
        assert_eq!(
            shown(text, (1.into(), 0.into())),
            Ok(String::from(
                "```gandr\nanswer : Integer\n```\n\nThe answer, said once."
            )),
            "the keyword answers the declaration it introduces"
        );
    }

    #[test]
    fn each_member_hovers_its_own_type()
    {
        let text =
            SourceText::from("module A {\n  def x = 1 ;\n}\nmodule B {\n  def x = \"one\" ;\n}\n");
        assert_eq!(
            shown(text, (1.into(), 6.into())),
            Ok(String::from("```gandr\nx : Integer\n```"))
        );
        assert_eq!(
            shown(text, (4.into(), 6.into())),
            Ok(String::from("```gandr\nx : String\n```"))
        );
        assert_eq!(
            shown(text, (0.into(), 7.into())),
            Ok(String::from("```gandr\nmodule A\n```")),
            "an undocumented module shows its head as written"
        );
    }

    #[test]
    fn html_hovers_colour_the_name_and_the_type()
    {
        let html = Style {
            form: Form::Sugared,
            spelling: Spelling::Unicode,
            markup: Markup::Html,
        };
        let coloured = |role: &str, text: &str| {
            format!("<span style=\"color:var(--vscode-gandr-hover-{role});\">{text}</span>")
        };
        let (text, at) = marker(SourceText::from(
            "def $0f(x: Integer) -> -F Integer { return x }\n",
        ));
        assert_eq!(
            styled(SourceText::from(text.as_str()), at, html),
            Ok(format!(
                "<pre><code>{} : {} {} {}</code></pre>",
                coloured("functionDef", "f"),
                coloured("typeBuiltin", "Integer"),
                coloured("operator", "=&gt;"),
                coloured("typeBuiltin", "Integer"),
            )),
            "the name in its editor colour, the sugared type in its roles, `>` escaped"
        );
        let (text, at) = marker(SourceText::from(
            "def f($0x: Integer) -> -F Integer { return x }\n",
        ));
        assert_eq!(
            styled(SourceText::from(text.as_str()), at, html),
            Ok(format!(
                "<pre><code>{} : {}</code></pre>",
                coloured("variableParam", "x"),
                coloured("typeBuiltin", "Integer"),
            )),
            "a binder in the parameter colour the editor gives it"
        );
        assert_eq!(
            styled(SourceText::from(text.as_str()), at, PLAIN),
            Ok(fenced(SourceText::from("x : Integer"))),
            "the markdown hover is the fenced block it always was"
        );
    }

    /// A described-member hover row: what the position is, the text, the
    /// line and character, and the expected hover.
    type Row<'text> = (
        &'text str,
        &'text str,
        (u32, u32),
        Result<String, hovered::Absent>,
    );

    #[test]
    fn a_described_member_hovers_its_own_type()
    {
        let data = "data NatDiv : Type {\n  Zero : NatDiv;\n  Succ : (n : NatDiv) --> NatDiv;\n  \
                    oper divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv);\n  \
                    rule divmod(m, Zero) ==> (Zero, m);\n}\n";
        let theory = "theory Cat {\n  sort Ob : Type;\n  sort Hom(dom : Ob, cod : Ob) : Type;\n  \
                    oper id : (a : Ob) --> Hom(a, a);\n  \
                    oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);\n  \
                    rule unitL : comp(id(a), f) ==> f;\n}\n";
        let rows: [Row<'_>; 15] = [
            (
                "a data family's name",
                data,
                (0, 6),
                Ok(fenced(SourceText::from("NatDiv : Type"))),
            ),
            (
                "a data family's keyword",
                data,
                (0, 1),
                Ok(fenced(SourceText::from("NatDiv : Type"))),
            ),
            (
                "a constant constructor",
                data,
                (1, 3),
                Ok(fenced(SourceText::from("Zero : NatDiv"))),
            ),
            (
                "a constructor with a field",
                data,
                (2, 3),
                Ok(fenced(SourceText::from("Succ : +U (NatDiv -> -F NatDiv)"))),
            ),
            (
                "a constructor's field",
                data,
                (2, 10),
                Ok(fenced(SourceText::from("n : NatDiv"))),
            ),
            (
                "a rule's head",
                data,
                (4, 8),
                Ok(fenced(SourceText::from(
                    "divmod : +U (NatDiv -> NatDiv -> -F #{NatDiv, NatDiv})",
                ))),
            ),
            (
                "a rule's arrow",
                data,
                (4, 23),
                Ok(fenced(SourceText::from("oriented left to right"))),
            ),
            (
                "a rule's pattern variable",
                data,
                (4, 14),
                Ok(fenced(SourceText::from("m : NatDiv"))),
            ),
            (
                "a rule's results",
                data,
                (4, 27),
                Ok(fenced(SourceText::from("#{NatDiv, NatDiv}"))),
            ),
            (
                "a member's keyword",
                data,
                (3, 3),
                Ok(fenced(SourceText::from(
                    "oper divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv)",
                ))),
            ),
            (
                "a field's parenthesis",
                data,
                (2, 9),
                Err(hovered::Absent::Untyped),
            ),
            (
                "an indexed sort",
                theory,
                (2, 8),
                Ok(fenced(SourceText::from("Hom : +U (Ob -> Ob -> -F Type)"))),
            ),
            (
                "an operation over the sorts before it",
                theory,
                (3, 8),
                Ok(fenced(SourceText::from(
                    "id : +U ((a : Ob) -> -F Hom(a, a))",
                ))),
            ),
            (
                "a law's application",
                theory,
                (5, 22),
                Ok(fenced(SourceText::from("Hom(a, a)"))),
            ),
            (
                "a theory member's keyword",
                theory,
                (5, 3),
                Ok(fenced(SourceText::from(
                    "rule unitL : comp(id(a), f) ==> f",
                ))),
            ),
        ];
        for (position, text, (line, character), expected) in rows {
            assert_eq!(
                shown(SourceText::from(text), (line.into(), character.into())),
                expected,
                "{position}"
            );
        }
    }

    #[test]
    fn a_theory_and_a_module_hover_as_written_1122_1124()
    {
        let model = "theory Semigroup {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> \
                     M;\n}\n\n/// A semigroup with a unit.\ntheory Monoid {\n  include \
                     Semigroup;\n  oper one : () --> M;\n  rule unitL : mul(one(), x) ==> \
                     x;\n}\n\nmodule Ints : Model(Semigroup) {\n  type M = Integer;\n  def \
                     mul(x : Integer, y : Integer) -> -F Integer { return y }\n}\n";
        let shaped = "theory Generated {\n  shape Two : 2 {\n    left = {0};\n  };\n  sort Val : \
                      Type;\n  oper zero : Val;\n  ext Cell = Val on left is zero;\n}\n\ntheory \
                      Wheel {\n  sort Nat : Type;\n  obs emit : (s : Nat, x : Nat) --> (y : \
                      Nat);\n  rule spin : (data stream : Nat) ==> (out : Nat) {\n    node : \
                      emit(state, stream) --> (out);\n    feed : (out) --> (state);\n  };\n}\n";
        let monoid = format!(
            "{}\n\nA semigroup with a unit.",
            fenced(SourceText::from(
                "theory Monoid {\n  include Semigroup;\n  oper one : () --> M;\n  rule unitL : \
                 mul(one(), x) ==> x;\n}"
            ))
        );
        let module = fenced(SourceText::from("module Ints : Model(Semigroup)"));
        let shape = fenced(SourceText::from("shape Two : 2 {\n  left = {0};\n}"));
        let rule = fenced(SourceText::from(
            "rule spin : (data stream : Nat) ==> (out : Nat)",
        ));
        let rows: [Row<'_>; 10] = [
            ("a theory's name", model, (6, 8), Ok(monoid.clone())),
            ("a theory's keyword", model, (6, 2), Ok(monoid)),
            (
                "an include's keyword",
                model,
                (7, 3),
                Ok(fenced(SourceText::from("include Semigroup"))),
            ),
            (
                "an include's name",
                model,
                (7, 12),
                Ok(fenced(SourceText::from("include Semigroup"))),
            ),
            ("a module's name", model, (12, 8), Ok(module.clone())),
            ("a module's ascription", model, (12, 22), Ok(module)),
            (
                "a type member",
                model,
                (13, 7),
                Ok(fenced(SourceText::from("type M = Integer"))),
            ),
            ("a shape's name", shaped, (1, 9), Ok(shape.clone())),
            ("a shape's face", shaped, (2, 5), Ok(shape)),
            ("a circuit rule's name", shaped, (12, 8), Ok(rule)),
        ];
        for (position, text, (line, character), expected) in rows {
            assert_eq!(
                shown(SourceText::from(text), (line.into(), character.into())),
                expected,
                "{position}"
            );
        }
    }
}
