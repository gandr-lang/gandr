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
//!   body a rule fills.
//! - **A use of a declaration the document writes that no entry types** — the
//!   theory an `include` or a `Model(…)` names — as that declaration's name
//!   answers, about the use; an `include`'s keyword likewise, about the
//!   `include`, and an `include` of a theory the document does not write as
//!   written.
//! - **The innermost typed node holding the cursor**, about its span: a term
//!   with its type, and, when an outer judgement checked it against a type
//!   spelled otherwise, that type after it; a binder with its name and the type
//!   of its uses, and a parameter's binder and its uses with the `///` run
//!   written before the parameter after a blank line; a written type with its
//!   text and its universe; a term the source writes as one name — a use, a
//!   constructor, a member — with that name before its type, as its binder
//!   answers. A keyword or a delimiter inside a term answers that term, so
//!   `return` and `{` answer the computation they open. A node spanning a whole
//!   declaration — the body's term the lowering writes over its declaration —
//!   answers as that declaration's name does, about its head when the cursor is
//!   there; a node spanning a source's run target answers as the run target:
//!   its outline name, then ` : ` and the thunk type the checker gave it.
//! - **The head of the innermost declaration holding the cursor** — from its
//!   declaring form's start to the brace opening its own body, or all of it
//!   when it has none — about the head, as for its name: the keyword that
//!   introduces it, the colon of its signature, a module's ascription, the
//!   layout before its body. A member's keyword answers the member. An
//!   attribute before the head answers the same, about the attributes. Inside a
//!   body, a member answers by its own entries, never the declaration around
//!   it.
//! - **An import**, anywhere in it, about the import: the import as written,
//!   then, for a path the document's closure read, the file it reads; for a
//!   path it did not, why — no file there, a file under another root, a file
//!   whose imports lead back, or one that does not parse. An address with a
//!   scheme names its tracking issue, as a read file's module documentation
//!   does.
//! - **A tile of a refused declaration or a refused source** answers what the
//!   lowering kept — a resolved use the line declaring what it refers to, a
//!   name what it names, any other tile its grammar rule — then the refusal:
//!   the declaration's hover, or the source's own. A declaration the checker
//!   refused counts, so a type written in a refused `data` declaration's
//!   constructor answers so, and the declaration's own hover names the
//!   checker's refusal after its type.
//! - **A declaration's own tile past its head**, about the tile, answers the
//!   innermost declaration or member holding it: a constructor's `:` or `-->`
//!   the constructor, a `data` declaration's or a module's brace the
//!   declaration. A rule a `data` declaration writes answers as written. A
//!   `rec` group's own tile answers the declarations the group writes, one to a
//!   line.
//! - **A root form that declares nothing** — the run target, or a stray — is a
//!   declaration of the outline's, keyed by its form as the engine keys its
//!   slot. A run target's tiles answer by their own entries; a stray's tiles,
//!   and the attributes before either form and the `;` after it, answer its
//!   outline name with its type or its refusal.
//! - **Any other tile** is one the engine typed nothing at: it answers what the
//!   lowering kept, then says so. The corpus sweep refuses a tile that hovers
//!   nothing or this.
//!
//! Layout and comments hover nothing, and so does a document whose grammar
//! did not build. Every type is spelled through the shared printer at 80
//! columns.
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
//! judgement parses it ([`Session::type_held_unit`]): its own text alone,
//! through the forms the recheck before it molded, laid after the tree of the
//! closure whose lowering the process holds, so the closure is neither molded
//! nor looked up again; the closure is laid out by the dispatcher's
//! [`lay_out_shadowed`], which reads each sibling an editor holds as its copy
//! and every other once per process. The document is then lowered after the
//! closure's judged arena and its own declarations typed on the checker's
//! state after the closure's, so a table costs the document's size, not its
//! closure's.
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
use gandr_surface_dispatcher::DeclaredHalf;
use gandr_surface_dispatcher::Laid;
use gandr_surface_dispatcher::NameKind;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::Shadows;
use gandr_surface_dispatcher::Subject;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::TypedSpan;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::laid;
use gandr_surface_dispatcher::lay_out_shadowed;
use gandr_surface_dispatcher::named_path;
use gandr_surface_lowering::DocumentationText;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Spelling;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::ClosureKey;
use gandr_surface_session::Session;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
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
use crate::reading::ImportAt;
use crate::reading::Reading;
use crate::reading::Tile;
use crate::reading::Written;
use crate::recheck::roles;
use crate::search::Found;
use crate::signature::Signatures;
use crate::tracking::Gap;

/// The page width a hover lays a type out at.
const HOVER_WIDTH: u32 = 80;

/// What a tile inside an accepted declaration answers, after what the lowering
/// kept, where the engine typed nothing at it: a sentence the corpus sweep
/// refuses.
const UNTYPED: &str = "The engine typed nothing here.";

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
    /// The document's path, as the hover was asked about it.
    document: PathBuf,
    /// What each of the document's path imports resolved to, in the order the
    /// document writes them; empty for a text typed alone.
    targets: Vec<ImportTarget>,
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
/// read, laid out over the import closure the dispatcher's
/// [`lay_out_shadowed`] lays `text` out in under `shadows`.
///
/// # Specification
/// - requires: nothing; `session` may have judged any revision.
/// - ensures: [`hovering_laid`] over that lay-out.
/// - provides: a table for a text no recheck laid out.
/// - fails: never; a refusal answers the empty table.
/// - panics: none.
/// - executable: none — as [`hovering_laid`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`hovering_laid`].
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
    hovering_laid(
        text,
        path,
        session,
        (
            &lay_out_shadowed(session.grammar(), path, classify(path), text, shadows),
            None,
        ),
    )
}

/// What the hovers of `text`, the document at `path` that `session` judges,
/// laid out as `laid`, read: one typed run per text, rather than one per hover,
/// and none when the judgement of `text` kept its table (`judged`).
///
/// # Specification
/// - requires: `laid` is the lay-out of `text` at `path` over its import
///   closure, or why it has none; `judged` is the table the judgement of that
///   lay-out kept
///   ([`Submission::take_table`](gandr_surface_session::Submission::take_table)),
///   or nothing.
/// - ensures: `judged` when it is held, else the type table
///   [`Session::type_held_unit`] answers over `laid` when `text` imports a
///   sibling by path — typed after the closure's judgement when the process
///   holds it — beside the closure's paths, else [`TypeTable::of_parsed`] over
///   `text` parsed through `session`'s form store ([`Session::parse_held`]),
///   beside no path; the store is left as it was, and the table is empty when
///   the text did not parse.
/// - provides: what a document copy keeps for its hovers, its definitions, its
///   completions and its signature help: the names read off the table once
///   ([`Names::of`]) and the heads read off the same parse
///   ([`Signatures::after`] when the tree is laid after the closure lowering
///   the process holds, so the closure's heads are read once per lowering, else
///   [`Signatures::of`]); a name an import brings in types at its use as its
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
/// - witness: `server::tests::a_hover_reads_the_lay_out_its_recheck_made_1403`
/// - witness: `recheck::tests::sweeps::a_recheck_keeps_the_table_its_hover_types_1521`
#[must_use]
pub fn hovering_laid<Store, Blocks>(
    text: SourceText<'_>,
    path: &Path,
    session: &Session<Store, Blocks>,
    (laid, judged): (&Maybe<Laid, laid::Absent>, Option<TypeTable>),
) -> Hovering
{
    let grammar = session.grammar();
    let (typed, paths, targets) = match *laid {
        Maybe::Present(ref laid) => {
            let mut signatures = Signatures::default();
            let read = |tree: &SyntaxTree<'_>, closure: Option<ClosureKey>| {
                if let Ok(roles) = roles() {
                    signatures = closure.as_ref().map_or_else(
                        || Signatures::of(grammar, roles, tree, &laid.unit),
                        |closure| {
                            Signatures::after(
                                grammar,
                                roles,
                                (tree, &laid.unit, laid.base),
                                closure,
                            )
                        },
                    );
                }
            };
            let revision = SourceText::from(laid.text.as_str());
            let table = match judged {
                Some(table) => {
                    let _parsed = session.read_held_unit(revision, (&laid.unit, laid.base), read);
                    Some(table)
                },
                None => session.type_held_unit(revision, (&laid.unit, laid.base), read),
            };
            let targets = laid
                .unit
                .sources()
                .last()
                .map(|importer| importer.imports().to_vec())
                .unwrap_or_default();
            (
                table.map(|table| (table, signatures)),
                laid.paths.clone(),
                targets,
            )
        },
        Maybe::Absent(_) => {
            let parsed = session.parse_held(text).ok();
            let signatures = parsed
                .as_ref()
                .zip(roles().ok())
                .map_or_else(Signatures::default, |(parsed, roles)| {
                    Signatures::of(grammar, roles, parsed.tree(), &Unit::single())
                });
            let table = judged.or_else(|| TypeTable::of_parsed(grammar, parsed?).ok());
            (
                table.map(|table| (table, signatures)),
                Vec::new(),
                Vec::new(),
            )
        },
    };
    let (table, signatures) = typed.unwrap_or_default();
    Hovering {
        names: Names::of(&table),
        table,
        paths,
        document: path.to_path_buf(),
        targets,
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
/// - ensures: in an import, its alias included, [`imported`]'s answer about the
///   import. Else, in a `//!` run of the document's own documentation the table
///   keeps, [`own_documentation`]'s answer about the run. Else, on a
///   declaration's name — from its first character to just past its last —
///   [`declared`]'s block about the name's range: the name and its type when
///   the table types it, then the checker's refusal when it refused the
///   declaration; the name and the refusal — the lowering's, or the checker's
///   where the lowering typed nothing — when the table holds one; else the
///   declaration as written, a theory and a module always so; then, after a
///   blank line, what a `deprecated` attribute marking the form states, and the
///   documentation the session filed for the form after another. A root form
///   that declares nothing — a run target, a stray — has no name to hover here.
///   On a member's name with no entry inside the member, the member as written,
///   about the name. Else, on a use of a declaration the text writes with no
///   entry inside the use — the theory an `include` or a `Model(…)` names — as
///   on that declaration's name, about the use; in a run a theory or a `data`
///   declaration writes that declares nothing — an `include`, a rule — with no
///   entry inside it and no orientation noted at the position, the same for the
///   first such use in the run, about the run, and else the run as written,
///   about it. Else, on the innermost typed node holding the position: inside a
///   member whose entries are none of them there, the member as written, about
///   the member; when the node spans a whole declaration — its body's term
///   written over the declaration, or a module's instantiation written over the
///   module (#405) — or a root form that declares nothing, as on that
///   declaration's name, about its head when the position is there and the
///   node's range otherwise; else a block of its type — a binder's name, a
///   written type's text or a term written as one name before ` : ` — and, for
///   a term checked against a type spelled otherwise, that type in a second
///   block; for a model standing where a model of a theory its own includes is
///   asked, the reduct the checker applies there, and for a model whose sorts
///   are manifest standing where a model of its theory is asked, the forgetting
///   map the checker applies there with the carriers it puts back, each applied
///   to the model, in a block after; for a parameter's binder or a use of it,
///   the `///` run written before the parameter after a blank line; about the
///   node's range. Else, in the head of a declaration — from its form's start
///   to the brace opening its own body, a member's keyword to its name — as on
///   its name, about the head, and in the attributes before the head, about
///   them. Else, on a tile, [`stubbed`]'s answer, about what it is about.
///   Absent in layout and comments. Every type is spelled in `style`'s form,
///   and every block is written as [`Code`] writes it in `style`'s markup.
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
///   a module's instantiation and two pattern tiles; a theory, an `include` of
///   an unwritten theory, a module's name and ascription, a type alias, a shape
///   and a circuit rule as written; an `include`'s keyword and name and a
///   `Model(…)`'s theory as the theory they name; a declaration and a written
///   type in HTML, coloured by their roles; a documented parameter at its
///   binder and at a use, and an undocumented one; a run target's call, its
///   `;`, a name and an argument inside it, a stray and its `;`, the attribute
///   of a run target the lowering refused, a model the checker carries to an
///   included theory's models by a reduct, and a manifest model it reads as its
///   theory's model by a forgetting map at the carriers it solves.
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::each_member_hovers_its_own_type`
/// - witness: `hover::tests::html_hovers_colour_the_name_and_the_type`
/// - witness: `hover::tests::a_decode_written_as_a_type_hovers_as_a_type_419`
/// - witness: `hover::tests::a_constructor_applied_inside_a_type_hovers_its_text_420`
/// - witness: `hover::tests::a_type_under_a_static_binder_hovers_its_text_404`
/// - witness: `hover::tests::a_module_instantiation_answers_itself_never_a_member_s_type_405`
/// - witness: `hover::tests::a_theory_and_a_module_hover_as_written_1122_1124`
/// - witness: `hover::tests::an_include_and_a_model_hover_the_theory_they_name_1123`
/// - witness: `hover::tests::the_parentheses_around_an_inverted_letter_answer_the_cons_pattern_408`
/// - witness: `hover::tests::a_sum_pattern_s_positional_label_answers_as_a_label_408`
/// - witness: `hover::tests::sweeps::every_corpus_tile_hovers_or_names_its_issue_1206`
/// - witness: `hover::tests::an_import_hovers_the_file_it_reads_1203`
/// - witness: `hover::tests::a_source_s_own_documentation_hovers_at_its_head_1365`
/// - witness: `hover::tests::a_documented_parameter_hovers_its_documentation_1116`
/// - witness: `hover::tests::a_run_target_and_a_stray_hover_as_declarations_2073`
/// - witness: `hover::tests::a_model_hovers_the_reduct_the_checker_applies_2031`
/// - witness: `hover::tests::a_manifest_model_hovers_the_forgetting_map_the_checker_applies_2130`
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
    if let Some(import) = reading.import_at(offset) {
        return imported(hovering, import, &quoted, style)
            .map_or(Maybe::Absent(hovered::Absent::Untyped), Maybe::Present);
    }
    if let Some(run) = reading.own_documentation_at(offset)
        && let Maybe::Present(written) = table.source_documentation(table.own_source())
    {
        return own_documentation(hovering, run, written, &quoted, style)
            .map_or(Maybe::Absent(hovered::Absent::Untyped), Maybe::Present);
    }
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
    // A root form that declares nothing has no name of its own: its tiles
    // answer by their entries, below.
    if let Some(named) = found.iter().find(|found| {
        found.written != Written::Root
            && found.symbol.selection_range.start <= position
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
            Written::Member | Written::Root => {},
        }
    }
    // A run a theory or a `data` declaration writes that declares nothing — an
    // `include`, a rule — answers the theory it names, below, else as written,
    // where nothing inside it is typed and no orientation is noted.
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
                && !table
                    .orientations()
                    .iter()
                    .any(|&(span, _)| span.start() <= offset && offset < span.end())
        });
    // A name that refers to a declaration this document writes and that no
    // entry types — the theory an `include` or a `Model(…)` names — answers as
    // that declaration's own name does, about the name; an `include`'s keyword
    // answers as the name after it, about the run.
    let referent_at = |byte: usize| match table.referent(ByteOffset::from(byte)) {
        Maybe::Present(found) => Some(found),
        Maybe::Absent(_) => None,
    };
    let referred = referent_at(at).or_else(|| {
        let (start, end) = unnamed?;
        (start .. end).find_map(referent_at)
    });
    if let Some((span, referent)) = referred
        && referent.source() == table.own_source()
        && !entered.is_some_and(|(from, to)| {
            usize::from(span.start()) <= from && to <= usize::from(span.end())
        })
        && let Ok(named) = Range::of_bytes(
            &index,
            RenderOffset::from(usize::from(referent.named().start())),
            RenderOffset::from(usize::from(referent.named().end())),
        )
        && let Some(declaration) = forms().find(|form| form.symbol.selection_range == named)
        && let Some((start, end)) = if span.start() <= offset && offset <= span.end() {
            Some((usize::from(span.start()), usize::from(span.end())))
        }
        else {
            unnamed
        }
        && let Ok(about) =
            Range::of_bytes(&index, RenderOffset::from(start), RenderOffset::from(end))
    {
        return Maybe::Present(declared(session, table, declaration, about, &quoted, style));
    }
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
        // module answers itself, never a member's type (#405). A run target's
        // entry over its whole form answers as the run target.
        if let Some(whole) = found
            .iter()
            .filter(|found| found.written != Written::Member)
            .rfind(|found| {
                let spanned = match found.written {
                    Written::Root => found.symbol.selection_range,
                    Written::Form | Written::Member => found.symbol.range,
                };
                range.start <= found.symbol.selection_range.start
                    && spanned.end <= range.end
                    && spanned.start <= position
                    && position <= spanned.end
            })
        {
            let about = if whole.head.start <= position && position < whole.head.end {
                whole.head
            }
            else {
                range
            };
            return Maybe::Present(declared(session, table, whole, about, &quoted, style));
        }
        let mut value = typed(&quoted, &entry, style.markup);
        // A parameter, written or used, answers the `///` run written before
        // it after its type.
        let parameter = match table.referent(entry.span().start()) {
            Maybe::Present((_, referent)) => hovering
                .signatures
                .parameter(referent.source(), referent.named()),
            Maybe::Absent(_) => None,
        }
        .or_else(|| {
            hovering
                .signatures
                .parameter(table.own_source(), entry.span())
        });
        if let Some(documented) = parameter {
            value.push_str("\n\n");
            value.push_str(<&str>::from(documented));
        }
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
    // stretch. A root form that declares nothing is the lowering's slot, so in
    // a source the lowering refused whole it answers the stub's refusal.
    let unlowered = matches!(table.refused_whole(), Maybe::Present(_));
    let enclosing = found.iter().rfind(|found| {
        found.symbol.range.start <= position
            && position < found.head.end
            && !(unlowered && found.written == Written::Root)
    });
    if let Some(enclosing) = enclosing {
        let about = if enclosing.head.start <= position {
            enclosing.head
        }
        else {
            Range {
                start: enclosing.symbol.range.start,
                end: enclosing.head.start,
            }
        };
        return Maybe::Present(match enclosing.written {
            Written::Form | Written::Root => {
                declared(session, table, enclosing, about, &quoted, style)
            },
            Written::Member => member(enclosing, about, &quoted, style),
        });
    }
    stubbed(session, hovering, reading, found, &quoted, offset, style)
        .map_or(Maybe::Absent(hovered::Absent::Untyped), Maybe::Present)
}

/// The hover of `import`, an import of the document `hovering` was built for,
/// about the import's bytes.
///
/// # Specification
/// - requires: `quoted` is the document `import` was read from.
/// - ensures: the import as written in a block; then, for a path the document's
///   closure read, the file it reads and, after a blank line, the documentation
///   that file writes of itself when it writes any; for a path it did not, why:
///   no file at the path, a file under another root, a file whose imports lead
///   back to the document, or a file that does not parse; for an address with a
///   scheme, its tracking line. None when the import's bytes split a character.
/// - provides: the import half of [`hover`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a resolved import of a documented file, a missing path
///   and an address with a scheme are asserted at their exact answers.
/// - witness: `hover::tests::an_import_hovers_the_file_it_reads_1203`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|hover| hover.contents.value.starts_with(style.markup.opener().0)))]
fn imported(
    hovering: &Hovering,
    import: ImportAt<'_>,
    quoted: &Quoted<'_>,
    style: Style,
) -> Option<Hover>
{
    let span = import.written.span;
    let start = RenderOffset::from(usize::from(span.start()));
    let range = Range::of_bytes(
        quoted.index,
        start,
        RenderOffset::from(usize::from(span.end())),
    )
    .ok()?;
    let mut code = Code::new(style.markup);
    let text = <&str>::from(quoted.text)
        .get(usize::from(start) .. usize::from(span.end()))
        .unwrap_or_default();
    quoted.quote(&mut code, SourceText::from(text), start);
    let resolution = import.ordinal.map_or_else(
        || Gap::Foreign.closing(),
        |ordinal| {
            let directory = hovering.document.parent().unwrap_or(&hovering.document);
            let file = named_path(&directory.join(import.written.uri.as_ref()));
            match hovering.targets.get(ordinal) {
                Some(&ImportTarget::Source(source)) => {
                    let read = format!(
                        "Reads `{}`.",
                        hovering
                            .paths
                            .get(usize::from(source))
                            .unwrap_or(&file)
                            .display()
                    );
                    match hovering.table.source_documentation(source) {
                        Maybe::Present(written) => format!("{read}\n\n{}", written.as_ref()),
                        Maybe::Absent(_) => read,
                    }
                },
                Some(&ImportTarget::Cycle) => format!(
                    "`{}` imports this document back, so neither is read.",
                    file.display()
                ),
                Some(&ImportTarget::Unresolved) | None => {
                    if !file.is_file() {
                        format!("No file at `{}`.", file.display())
                    }
                    else if classify(&file) != classify(&hovering.document) {
                        format!(
                            "`{}` is under another root than this document, so it is not read.",
                            file.display()
                        )
                    }
                    else {
                        format!(
                            "`{}` does not parse, so nothing it declares is read.",
                            file.display()
                        )
                    }
                },
            }
        },
    );
    Some(Hover {
        contents: MarkupContent {
            kind: "markdown",
            value: format!("{}\n\n{resolution}", code.block()),
        },
        range,
    })
}

/// The hover of `run`, a `//!` run of the document `hovering` was built for,
/// whose source wrote `written` of itself.
///
/// # Specification
/// - requires: `quoted` is the document `run` was read from.
/// - ensures: the document's file name in a block, then `written` after a blank
///   line, about the run's bytes. None when the run's bytes split a character.
/// - provides: the head-of-file half of [`hover`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a position in a source's own run answers the file and the
///   text the table keeps, and a word in an ordinary comment beside it answers
///   nothing.
/// - witness: `hover::tests::a_source_s_own_documentation_hovers_at_its_head_1365`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|hover| hover.contents.value.starts_with(style.markup.opener().0)))]
fn own_documentation(
    hovering: &Hovering,
    run: ByteSpan,
    written: &DocumentationText,
    quoted: &Quoted<'_>,
    style: Style,
) -> Option<Hover>
{
    let range = Range::of_bytes(
        quoted.index,
        RenderOffset::from(usize::from(run.start())),
        RenderOffset::from(usize::from(run.end())),
    )
    .ok()?;
    let mut code = Code::new(style.markup);
    let name = hovering.document.file_name().map_or_else(
        || format!("{}", hovering.document.display()),
        |name| name.to_string_lossy().into_owned(),
    );
    code.plain(SourceText::from(name.as_str()));
    Some(Hover {
        contents: MarkupContent {
            kind: "markdown",
            value: format!("{}\n\n{}", code.block(), written.as_ref()),
        },
        range,
    })
}

/// How a tile the table types nothing at stands: inside a refused
/// declaration, in a source the lowering refused as a whole, in a source the
/// table holds nothing for, one of a declaration's own tiles, or at a form the
/// engine typed nothing at.
#[derive(Clone, Copy, Debug)]
enum Standing<'found>
{
    /// Inside this declaration, the innermost refused one holding the tile.
    Refused(&'found Declaration),
    /// In a source the lowering refused as a whole.
    Whole,
    /// In a source the table holds nothing for, refused by no lowering.
    Empty,
    /// One of this declaration's or member's own tiles, the innermost holding
    /// it.
    Own(&'found Declaration),
    /// One of a form's own tiles that is no declaration's but holds these,
    /// the declarations the form writes: a `rec` group's.
    Group(&'found [Declaration]),
    /// At a form the engine typed nothing at, inside an accepted declaration
    /// or none: an engine gap, which the corpus sweep refuses.
    Untyped,
}

/// Where a hover has nothing typed to show: the tile holding a position and
/// how it stands.
#[derive(Clone, Copy, Debug)]
struct Stub<'found>
{
    /// The tile holding the position.
    tile: Tile,
    /// How the tile stands.
    standing: Standing<'found>,
}

/// The stub at `offset`, by the first standing that holds it: inside a
/// refused declaration — a root form's that declares nothing among them — in
/// a source refused as a whole, in a source the table holds nothing for, a
/// tile the innermost declaration or member holding it writes itself, a tile
/// of a form that writes declarations and is none itself, else at a form the
/// engine typed nothing at, an engine gap. An import answers before any
/// stub, by [`imported`].
///
/// # Specification
/// - requires: `found` and `quoted` are of the text `reading` read, and `table`
///   was typed over it.
/// - ensures: none when no tile holds `offset` — in layout or a comment;
///   otherwise the tile holding it with the first standing that holds it.
/// - provides: what [`hover`] answers where the engine typed nothing.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every tile of every corpus source hovers.
/// - witness: `hover::tests::sweeps::every_corpus_tile_hovers_or_names_its_issue_1206`
#[must_use]
#[spec(ensures: |ret| ret.as_ref().is_none_or(|found| found.tile.span.start() <= offset && offset < found.tile.span.end()))]
fn stub<'found>(
    table: &TypeTable,
    reading: &Reading,
    found: &'found [Declaration],
    quoted: &Quoted<'_>,
    offset: ByteOffset,
    style: Style,
) -> Option<Stub<'found>>
{
    let tile = reading.tile_at(offset)?;
    let page = PageWidth::from(HOVER_WIDTH);
    let printed = style.printed();
    let holds = |declaration: &&Declaration| {
        ByteOffset::from(usize::from(
            declaration.symbol.range.start.byte(quoted.index),
        )) <= offset
            && offset
                < ByteOffset::from(usize::from(declaration.symbol.range.end.byte(quoted.index)))
    };
    let within = |declaration: &Declaration| {
        tile.form.start()
            <= ByteOffset::from(usize::from(
                declaration.symbol.range.start.byte(quoted.index),
            ))
            && ByteOffset::from(usize::from(declaration.symbol.range.end.byte(quoted.index)))
                <= tile.form.end()
    };
    let refused = found
        .iter()
        .filter(|declaration| declaration.written != Written::Member && holds(declaration))
        .rfind(|declaration| {
            declaration
                .key
                .is_some_and(|key| matches!(table.refusal(key), Maybe::Present(_)))
        });
    let standing = refused.map_or_else(
        || {
            if matches!(table.refused_whole(), Maybe::Present(_)) {
                Standing::Whole
            }
            else if table.entries(page, printed).next().is_none()
                && table.declarations(page, printed).next().is_none()
            {
                Standing::Empty
            }
            else if let Some(holder) = found
                .iter()
                .rfind(|declaration| tile.declares && holds(declaration))
            {
                Standing::Own(holder)
            }
            else if let Some(first) = found
                .iter()
                .position(|declaration| tile.declares && within(declaration))
            {
                let count = found
                    .get(first ..)
                    .unwrap_or_default()
                    .iter()
                    .take_while(|declaration| within(declaration))
                    .count();
                Standing::Group(
                    found
                        .get(first .. first.saturating_add(count))
                        .unwrap_or_default(),
                )
            }
            else {
                Standing::Untyped
            }
        },
        Standing::Refused,
    );
    Some(Stub { tile, standing })
}

/// The hover of the stub at `offset`.
///
/// # Specification
/// - requires: as [`stub`].
/// - ensures: none where [`stub`] finds none. Inside a refused declaration,
///   [`kept`]'s answer, then the declaration's hover as [`declared`] writes it,
///   its refusal among it. In a source refused as a whole, [`kept`]'s answer,
///   then the lowering's refusal. In a source the table holds nothing for,
///   [`kept`]'s answer and that the engine holds nothing for it. On a
///   declaration's own tile, about the tile, the declaration's hover as
///   [`declared`] writes it, or a member's as [`member`] does. On a tile of a
///   form that writes declarations, about the tile, each declaration as
///   written, one to a line, then the form's rule named. At a form the engine
///   typed nothing at, [`kept`]'s answer, then [`UNTYPED`].
/// - provides: the half of [`hover`] where the engine typed nothing.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — as [`stub`]; L3 — a binder's use, a declaration's use and
///   a keyword inside a refused declaration, a tile of a source refused whole,
///   and the own tiles of a `data` declaration, a constructor, a `module` and a
///   `rec` are asserted at their exact answers.
/// - witness: `hover::tests::sweeps::every_corpus_tile_hovers_or_names_its_issue_1206`
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::a_refused_declaration_hovers_what_the_lowering_kept_1201`
/// - witness: `hover::tests::a_declaration_s_own_tile_hovers_the_declaration_1202`
/// - witness: `hover::tests::a_checker_refused_declaration_hovers_its_refusal_1204`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|hover| hover.contents.value.starts_with(style.markup.opener().0)))]
fn stubbed<Store, Blocks>(
    session: &Session<Store, Blocks>,
    hovering: &Hovering,
    reading: &Reading,
    found: &[Declaration],
    quoted: &Quoted<'_>,
    offset: ByteOffset,
    style: Style,
) -> Option<Hover>
{
    let table = &hovering.table;
    let Stub { tile, standing } = stub(table, reading, found, quoted, offset, style)?;
    let (about, mut value) = match standing {
        Standing::Own(holder) => {
            let range = Range::of_bytes(
                quoted.index,
                RenderOffset::from(usize::from(tile.span.start())),
                RenderOffset::from(usize::from(tile.span.end())),
            )
            .ok()?;
            let shown = match holder.written {
                Written::Form | Written::Root => {
                    declared(session, table, holder, range, quoted, style)
                },
                Written::Member => member(holder, range, quoted, style),
            };
            (tile.span, shown.contents.value)
        },
        Standing::Group(held) => {
            let mut code = Code::new(style.markup);
            for (at, declaration) in held
                .iter()
                .filter(|declaration| declaration.written == Written::Form)
                .enumerate()
            {
                if at > 0 {
                    code.plain(SourceText::from("\n"));
                }
                written(&mut code, declaration, quoted);
            }
            (
                tile.span,
                format!(
                    "{}\n\nThe declarations this `{}` writes together.",
                    code.block(),
                    tile.rule
                ),
            )
        },
        Standing::Refused(_) | Standing::Whole | Standing::Empty | Standing::Untyped => {
            kept(hovering, quoted, tile, offset, style)
        },
    };
    let range = Range::of_bytes(
        quoted.index,
        RenderOffset::from(usize::from(about.start())),
        RenderOffset::from(usize::from(about.end())),
    )
    .ok()?;
    match standing {
        Standing::Refused(refused) => {
            value.push_str("\n\n");
            value.push_str(
                &declared(session, table, refused, range, quoted, style)
                    .contents
                    .value,
            );
        },
        Standing::Whole => {
            if let Maybe::Present(refusal) = table.refused_whole() {
                value.push_str("\n\nThe engine refuses this source as a whole: ");
                value.push_str(<&str>::from(refusal));
            }
        },
        Standing::Empty => {
            value.push_str("\n\nThe engine holds nothing for this source.");
        },
        Standing::Untyped => {
            value.push_str("\n\n");
            value.push_str(UNTYPED);
        },
        Standing::Own(_) | Standing::Group(_) => {},
    }
    Some(Hover {
        contents: MarkupContent {
            kind: "markdown",
            value,
        },
        range,
    })
}

/// What a tile answers from what the lowering kept where nothing is typed,
/// and the bytes it is about.
///
/// # Specification
/// - requires: `quoted` is the document `hovering` was built for, and `tile`
///   one of its tiles holding `offset`.
/// - ensures: on a use the lowering resolved, about the use, the line that
///   writes the name of what it refers to, trimmed, in a block — a
///   declaration's signature, a constructor's own line, a binder's — then what
///   that is and the line it is written at, and the file when another source
///   writes it. On a name a declaration, a constructor or a binder is written
///   by, about the name, the name in a block and what it names here. Else,
///   about the tile, the tile in a block and the grammar's rule it is a tile
///   of.
/// - provides: the answer a refused declaration and a refused source give.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`stubbed`].
/// - witness: `hover::tests::a_refused_declaration_hovers_what_the_lowering_kept_1201`
/// - witness: `hover::tests::a_checker_refused_declaration_hovers_its_refusal_1204`
#[spec(ensures: |ref ret| ret.1.starts_with(style.markup.opener().0) && usize::from(ret.0.end()) <= <&str>::from(quoted.text).len())]
fn kept(
    hovering: &Hovering,
    quoted: &Quoted<'_>,
    tile: Tile,
    offset: ByteOffset,
    style: Style,
) -> (ByteSpan, String)
{
    let table = &hovering.table;
    let own = table.own_source();
    let kind = |referent: Referent| {
        table
            .declared_names()
            .iter()
            .find(|&&(named, _)| named == referent)
            .map_or("A binder", |&(_, kind)| match kind {
                NameKind::Family => "A family",
                NameKind::Constructor => "A constructor",
                NameKind::Value => "A declaration",
            })
    };
    let mut code = Code::new(style.markup);
    let quote = |code: &mut Code, span: ByteSpan| {
        let start = RenderOffset::from(usize::from(span.start()));
        let text = <&str>::from(quoted.text)
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .unwrap_or_default();
        quoted.quote(code, SourceText::from(text), start);
    };
    if let Maybe::Present((span, referent)) = table.referent(offset) {
        let site = table.half(referent, DeclaredHalf::Signature);
        let written = table
            .source_text(site.source())
            .map(<&str>::from)
            .unwrap_or_default();
        let named = usize::from(site.named().start());
        let before = written.get(.. named).unwrap_or_default();
        let from = before
            .rfind('\n')
            .map_or(0, |newline| newline.saturating_add(1));
        let to = written
            .get(named ..)
            .and_then(|after| after.find('\n'))
            .map_or(written.len(), |newline| named.saturating_add(newline));
        let holding = written.get(from .. to).unwrap_or_default();
        let indent = holding.len().saturating_sub(holding.trim_start().len());
        let shown = holding.trim();
        let start = from.saturating_add(indent);
        if site.source() == own {
            quote(
                &mut code,
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start.saturating_add(shown.len())),
                )
                .unwrap_or_else(|_| site.named()),
            );
        }
        else {
            code.plain(SourceText::from(shown));
        }
        let line = before.matches('\n').count().saturating_add(1);
        let place = if site.source() == own {
            format!("written at line {line}.")
        }
        else {
            hovering.paths.get(usize::from(site.source())).map_or_else(
                || format!("written at line {line} of an imported source."),
                |path| format!("written at line {line} of `{}`.", path.display()),
            )
        };
        return (
            span,
            format!("{}\n\n{}, {place}", code.block(), kind(referent)),
        );
    }
    if let Maybe::Present(referent) = table.named_at(offset)
        && referent.source() == own
    {
        quote(&mut code, referent.named());
        return (
            referent.named(),
            format!("{}\n\n{}, written here.", code.block(), kind(referent)),
        );
    }
    quote(&mut code, tile.span);
    (
        tile.span,
        format!("{}\n\nA tile of `{}`.", code.block(), tile.rule),
    )
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
///   A root form that declares nothing is named by what it writes, as the
///   outline names it. For one `table` holds the lowering's refusal of instead:
///   the name, then that refusal after a blank line. Otherwise, a theory and a
///   module always among them, the declaration as [`written`] writes it, a
///   theory with its members. Where `table` holds the checker's refusal of a
///   declaration it does not hold the lowering's refusal of, that refusal after
///   a blank line. Where a `deprecated` attribute marks the form, `deprecated`,
///   with the version after `since` and the note after a colon when the
///   attribute states them, after a blank line. Then the documentation
///   `session` filed under the form's key after a blank line.
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
/// - witness: `hover::tests::a_checker_refused_declaration_hovers_its_refusal_1204`
/// - witness: `hover::tests::a_deprecated_declaration_hovers_its_note`
/// - witness: `hover::tests::a_run_target_and_a_stray_hover_as_declarations_2073`
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
    let checked = key
        .filter(|_| !matches!(held, Some(Declared::Refused(_))))
        .and_then(|key| match table.refusal(key) {
            Maybe::Present(refusal) => Some(refusal),
            Maybe::Absent(_) => None,
        });
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
    if let Some(refusal) = checked {
        value.push_str("\n\nrefused: ");
        value.push_str(<&str>::from(refusal));
    }
    if let Some(stated) = key.and_then(|key| session.deprecation(key)) {
        value.push_str("\n\ndeprecated");
        if let Some(ref since) = stated.since {
            value.push_str(" since ");
            value.push_str(since);
        }
        if let Some(ref note) = stated.note {
            value.push_str(": ");
            value.push_str(note);
        }
    }
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
///   so; for a model standing where a model of a theory its own includes is
///   asked or a model whose sorts are manifest standing where a model of its
///   theory is asked, a block of the reduct or the forgetting map the checker
///   applies there, applied to the term as the explicit form writes it — its
///   text when it is one line, else `…` — after a line saying so.
/// - provides: the node half of [`hover`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a use, a binder, a written type, a literal, a mismatched
///   term, a model standing at an included theory's models and a manifest model
///   standing at its theory's models are asserted at their exact texts.
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::html_hovers_colour_the_name_and_the_type`
/// - witness: `hover::tests::a_model_hovers_the_reduct_the_checker_applies_2031`
/// - witness: `hover::tests::a_manifest_model_hovers_the_forgetting_map_the_checker_applies_2130`
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
    if let Maybe::Present(map) = entry.crossed() {
        let argument = <&str>::from(quoted.text)
            .get(start .. end)
            .filter(|written| !written.contains('\n'))
            .unwrap_or("…");
        let mut applied = Code::new(markup);
        applied.printed(
            SourceText::from(map.around(SourceFragment::from(argument)).as_str()),
            Host::Term,
        );
        value.push_str("\n\nthe checker applies\n\n");
        value.push_str(&applied.block());
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
            .join("../../corpus/model/identity/circle-elim.gandr");
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
            .join("../../corpus/model/identity/circle-elim.gandr");
        let written = std::fs::read_to_string(&path).expect("the corpus source is read");
        let text = SourceText::from(written.as_str());
        let line = written
            .find("def joined : Path(")
            .expect("the source declares `joined`");
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
        let ty = "Path(Path(Circle, Base, Base), loop then here(Base), loop)";
        let named = at(line.saturating_add("def jo".len()));
        assert!(
            named.starts_with(&fenced(SourceText::from(format!("joined : {ty}").as_str()))),
            "the name prints the type as written: {named}"
        );
        assert_eq!(
            at(line.saturating_add("def joined : Pa".len())),
            fenced(SourceText::from(format!("{ty} : Type").as_str())),
            "the written type prints the same text"
        );
    }

    /// #2031: a model standing where a model of a theory its own includes is
    /// asked hovers the reduct the checker applies there, applied to it as
    /// the explicit form writes it; a model with manifest sorts crosses to an
    /// included theory's model by a forgetting map composed with a reduct,
    /// which the explicit form leaves to the checker, and the function called
    /// names none.
    #[test]
    fn a_model_hovers_the_reduct_the_checker_applies_2031()
    {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/include/reduct.gandr");
        let written = std::fs::read_to_string(&path).expect("the corpus source is read");
        let text = SourceText::from(written.as_str());
        let index = LineIndex::new(written.as_str().into());
        let session = checked(text);
        let reading = Reading::of(text);
        let hovering = hovering(text, &path, &session, &gandr_surface_dispatcher::Unshadowed);
        let at = |needle: &str, past: usize| {
            let offset = written
                .find(needle)
                .expect("the source writes the call")
                .saturating_add(past);
            let position = Position::of_byte(&index, RenderOffset::from(offset))
                .expect("the offset is on a boundary");
            match hover(text, &session, &reading, &hovering, position, PLAIN) {
                Maybe::Present(shown) => shown.contents.value,
                Maybe::Absent(reason) => panic!("`{needle}` hovers nothing: {reason:?}"),
            }
        };
        let applied = |call: &str| format!("\n\nthe checker applies\n\n{}", fenced(call.into()));
        for (needle, call) in [
            ("multiplies(endoMonoid)", "Monoid.Semigroup(endoMonoid)"),
            ("multiplies(m)", "UnitAndZero.Semigroup(m)"),
        ] {
            let shown = at(needle, "multiplies(".len());
            assert!(
                shown.ends_with(&applied(call)),
                "`{needle}` names the reduct the checker applies: {shown}"
            );
        }
        for (needle, past) in [
            ("multiplies(endoManifest)", "multiplies(".len()),
            ("multiplies(endoMonoid)", 0),
        ] {
            let shown = at(needle, past);
            assert!(
                !shown.contains("the checker applies"),
                "`{needle}` at {past} names no reduct: {shown}"
            );
        }
    }

    /// #2130: a model whose sorts are manifest standing where a model of its
    /// theory is asked hovers the forgetting map the checker applies there,
    /// with the carriers it puts back, applied to it as the explicit form
    /// writes it; a model whose carrier is selected off a binder names none.
    #[test]
    fn a_manifest_model_hovers_the_forgetting_map_the_checker_applies_2130()
    {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/identity/model-counter-manifest.gandr");
        let written = std::fs::read_to_string(&path).expect("the corpus source is read");
        let text = SourceText::from(written.as_str());
        let index = LineIndex::new(written.as_str().into());
        let session = checked(text);
        let reading = Reading::of(text);
        let hovering = hovering(text, &path, &session, &gandr_surface_dispatcher::Unshadowed);
        let at = |needle: &str, past: usize| {
            let offset = written
                .find(needle)
                .expect("the source writes the call")
                .saturating_add(past);
            let position = Position::of_byte(&index, RenderOffset::from(offset))
                .expect("the offset is on a boundary");
            match hover(text, &session, &reading, &hovering, position, PLAIN) {
                Maybe::Present(shown) => shown.contents.value,
                Maybe::Absent(reason) => panic!("`{needle}` hovers nothing: {reason:?}"),
            }
        };
        let applied = |call: &str| format!("\n\nthe checker applies\n\n{}", fenced(call.into()));
        for (needle, past, call) in [
            (
                "observe(upManifest)",
                "observe(".len(),
                "forget[sort C = +{Unit, Bool}](upManifest) at Model(Counter)",
            ),
            (
                "observeShown(upBoth)",
                "observeShown(".len(),
                "forget[sort C = +{Unit, Bool}, sort R = Integer](upBoth) at Model(ReadCounter)",
            ),
        ] {
            let shown = at(needle, past);
            assert!(
                shown.ends_with(&applied(call)),
                "`{needle}` names the forgetting map the checker applies: {shown}"
            );
        }
        let shown = at("observe(b)", "observe(".len());
        assert!(
            !shown.contains("the checker applies"),
            "`b`, whose carrier is selected off a binder, names no map: {shown}"
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
                    "ring : #{n : Integer, v : Path(Integer, n, n)}",
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
    fn a_builtin_namespace_hovers_the_path_it_qualifies_1170()
    {
        let call = |marked_at: &str| {
            marked(SourceText::from(
                format!(
                    "def quotientOf(c : Integer) -> -F Integer {{\n  run lead <- {marked_at}(c, \
                     64);\n  return lead\n}}\n"
                )
                .as_str(),
            ))
        };
        let path = call("int.di$0v");
        assert_eq!(
            path,
            Ok(fenced(SourceText::from(
                "+U (Integer -> Integer -> -F Integer)"
            ))),
            "the primitive answers its type"
        );
        assert_eq!(call("in$0t.div"), path, "its namespace answers as the path");
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
    fn a_deprecated_declaration_hovers_its_note()
    {
        let text = SourceText::from(
            "/// The answer.\n@[ deprecated(#{ since = \"0.2\", note = \"use `other`\" }) ]\ndef \
             answer = 42 ;\n@[ deprecated ] def bare = 1 ;\ndef other = 2 ;\n",
        );
        assert_eq!(
            shown(text, (2.into(), 5.into())),
            Ok(String::from(
                "```gandr\nanswer : Integer\n```\n\ndeprecated since 0.2: use `other`\n\nThe \
                 answer."
            )),
            "the deprecation stands before the documentation"
        );
        assert_eq!(
            shown(text, (3.into(), 21.into())),
            Ok(String::from("```gandr\nbare : Integer\n```\n\ndeprecated")),
            "a bare mark states neither the version nor the note"
        );
        assert_eq!(
            shown(text, (4.into(), 5.into())),
            Ok(String::from("```gandr\nother : Integer\n```")),
            "an unmarked declaration says nothing of it"
        );
    }

    /// #1116: a parameter, at its binder and at a use, hovers its type and
    /// the `///` run written before it; one with none hovers its type alone.
    #[test]
    fn a_documented_parameter_hovers_its_documentation_1116()
    {
        let text = SourceText::from(
            "def plus(\n  /// The first summand.\n  n : Integer,\n  m : Integer\n) -> -F Integer \
             {\n  return n\n}\ndef id(\n  k : Integer\n) -> -F Integer {\n  return k\n}\n",
        );
        let documented = Ok(String::from(
            "```gandr\nn : Integer\n```\n\nThe first summand.",
        ));
        assert_eq!(shown(text, (2.into(), 2.into())), documented, "the binder");
        assert_eq!(shown(text, (5.into(), 9.into())), documented, "a use");
        assert_eq!(
            shown(text, (8.into(), 2.into())),
            Ok(String::from("```gandr\nk : Integer\n```")),
            "an undocumented parameter"
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
    fn a_documented_module_hovers_its_documentation_1135()
    {
        let text = SourceText::from(
            "/// A module.\nmodule A {\n  /// A def.\n  def x = 1 ;\n  /// Nested.\n  module B { \
             def y = 2 ; }\n}\n",
        );
        assert_eq!(
            shown(text, (1.into(), 7.into())),
            Ok(String::from("```gandr\nmodule A\n```\n\nA module.")),
            "a module shows its head, then its own documentation"
        );
        assert_eq!(
            shown(text, (5.into(), 9.into())),
            Ok(String::from("```gandr\nmodule B\n```\n\nNested.")),
            "a nested module shows its own"
        );
        assert_eq!(
            shown(text, (3.into(), 6.into())),
            Ok(String::from("```gandr\nx : Integer\n```\n\nA def.")),
            "a member keeps its own, not its module's"
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

    /// A declaration's own tile answers what holds it: a constructor's its
    /// constructor, a rule's the rule as written, a `data` declaration's or a
    /// module's brace the declaration, and a `rec` group's tile the
    /// declarations the group writes. None names a tracking issue.
    #[test]
    fn a_declaration_s_own_tile_hovers_the_declaration_1202()
    {
        let data = "data NatDiv : Type {\n  Zero : NatDiv;\n  Succ : (n : NatDiv) --> NatDiv;\n  \
                    oper divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv);\n  \
                    rule divmod(m, Zero) ==> (Zero, m);\n}\n";
        let module = "module Ints {\n  def one : Integer ;\n  def one = 1 ;\n}\n";
        let rec = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\nrec {\n  def \
                   rec ping(n : Nat) -> -F Nat { become pong(n) }\n  def rec pong(n : Nat) -> \
                   -F Nat { return n }\n}\n";
        let succ = fenced(SourceText::from("Succ : (n : NatDiv) --> NatDiv"));
        let zero = fenced(SourceText::from("Zero : NatDiv"));
        let rule = fenced(SourceText::from("rule divmod(m, Zero) ==> (Zero, m)"));
        let ints = fenced(SourceText::from("module Ints"));
        let group = format!(
            "{}\n\nThe declarations this `rec_block` writes together.",
            fenced(SourceText::from(
                "def rec ping(n : Nat) -> -F Nat\ndef rec pong(n : Nat) -> -F Nat"
            ))
        );
        let rows: [Row<'_>; 11] = [
            (
                "a constructor's parenthesis",
                data,
                (2, 9),
                Ok(succ.clone()),
            ),
            ("a constructor's colon", data, (1, 7), Ok(zero.clone())),
            ("a constructor's semicolon", data, (1, 15), Ok(zero)),
            ("a constructor's arrow", data, (2, 22), Ok(succ)),
            (
                "a data declaration's closing brace",
                data,
                (5, 0),
                Ok(fenced(SourceText::from("NatDiv : Type"))),
            ),
            ("a rule's keyword", data, (4, 2), Ok(rule)),
            (
                "a module's opening brace",
                module,
                (0, 12),
                Ok(ints.clone()),
            ),
            ("a module's closing brace", module, (3, 0), Ok(ints)),
            ("a rec group's keyword", rec, (4, 0), Ok(group.clone())),
            (
                "a rec group's opening brace",
                rec,
                (4, 4),
                Ok(group.clone()),
            ),
            ("a rec group's closing brace", rec, (7, 0), Ok(group)),
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
    fn a_described_member_hovers_its_own_type()
    {
        let data = "data NatDiv : Type {\n  Zero : NatDiv;\n  Succ : (n : NatDiv) --> NatDiv;\n  \
                    oper divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv);\n  \
                    rule divmod(m, Zero) ==> (Zero, m);\n}\n";
        let theory = "theory Cat {\n  sort Ob : Type;\n  sort Hom(dom : Ob, cod : Ob) : Type;\n  \
                    oper id : (a : Ob) --> Hom(a, a);\n  \
                    oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);\n  \
                    rule unitL : comp(id(a), f) ==> f;\n}\n";
        let rows: [Row<'_>; 14] = [
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
        let rows: [Row<'_>; 8] = [
            ("a theory's name", model, (6, 8), Ok(monoid.clone())),
            ("a theory's keyword", model, (6, 2), Ok(monoid)),
            ("a module's name", model, (12, 8), Ok(module.clone())),
            ("a module's ascription", model, (12, 16), Ok(module)),
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

    #[test]
    fn an_include_and_a_model_hover_the_theory_they_name_1123()
    {
        let model = "theory Semigroup {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> \
                     M;\n}\n\ntheory Monoid {\n  include Semigroup;\n  include Unwritten;\n  \
                     oper one : () --> M;\n}\n\nmodule Ints : Model(Semigroup) {\n  type M = \
                     Integer;\n  def mul(x : Integer, y : Integer) -> -F Integer { return y \
                     }\n}\n";
        let semigroup = Ok(fenced(SourceText::from(
            "theory Semigroup {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n}",
        )));
        let rows: [Row<'_>; 5] = [
            ("the theory's own name", model, (0, 9), semigroup.clone()),
            ("an include's name", model, (6, 12), semigroup.clone()),
            ("an include's keyword", model, (6, 3), semigroup.clone()),
            ("a model's theory", model, (11, 22), semigroup),
            (
                "an include of a theory nowhere written",
                model,
                (7, 12),
                Ok(fenced(SourceText::from("include Unwritten"))),
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

    /// A declaration the checker refused answers its type and then the
    /// checker's refusal, at its name and at a use of it; a type written in its
    /// constructor answers its rule and then the declaration's hover, the
    /// refusal among it. None names a tracking issue.
    #[test]
    fn a_checker_refused_declaration_hovers_its_refusal_1204()
    {
        let source = "data Small : Type {\n  Pick : (a : Type, f : +U (a -> -F Small)) --> \
                      Small;\n}\n";
        let declared = "```gandr\nSmall : Type\n```\n\nrefused: a constructor field exceeds the declared \
             universe";
        let rows = [
            ("the declaration's name", (0, 5), String::from(declared)),
            (
                "a field's parenthesis",
                (1, 27),
                format!("```gandr\n(\n```\n\nA tile of `parenthesized_type`.\n\n{declared}"),
            ),
            (
                "a field's thunk type",
                (1, 24),
                format!("```gandr\n+U\n```\n\nA tile of `u_type`.\n\n{declared}"),
            ),
            ("a use of the declaration", (1, 37), String::from(declared)),
        ];
        for (position, (line, character), expected) in rows {
            assert_eq!(
                shown(SourceText::from(source), (line.into(), character.into())),
                Ok(expected),
                "{position}"
            );
        }
    }

    /// Inside a declaration the lowering refused, a tile answers what the
    /// lowering kept — a constructor's use the line declaring it, a keyword
    /// its rule, and a parameter's use inside the refused call its binder
    /// (#1265) — followed by the declaration's hover with its refusal; a tile
    /// of a source refused as a whole answers its rule and that refusal. None
    /// names a tracking issue.
    #[test]
    fn a_refused_declaration_hovers_what_the_lowering_kept_1201()
    {
        let source = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef bad(x \
                      : Nat) -> -F Nat {\n  return Succ(x, x)\n}\n";
        let refused = "```gandr\nbad\n```\n\nrefused: `call_expression`, read as a value, does not take 2 \
             operands";
        let rows = [
            (
                "a constructor's use",
                (5, 9),
                format!(
                    "```gandr\nSucc : (n : Nat) --> Nat;\n```\n\nA constructor, written at line \
                     3.\n\n{refused}"
                ),
            ),
            (
                "a keyword",
                (5, 2),
                format!("```gandr\nreturn\n```\n\nA tile of `return_expression`.\n\n{refused}"),
            ),
            (
                "a parameter's use inside the refused call",
                (5, 14),
                format!(
                    "```gandr\ndef bad(x : Nat) -> -F Nat {{\n```\n\nA binder, written at line \
                     5.\n\n{refused}"
                ),
            ),
        ];
        for (position, (line, character), expected) in rows {
            assert_eq!(
                shown(SourceText::from(source), (line.into(), character.into())),
                Ok(expected),
                "{position}"
            );
        }
        assert_eq!(
            shown(SourceText::from("@[ checks ]\n"), (0.into(), 0.into())),
            Ok(String::from(
                "```gandr\n@[\n```\n\nA tile of `attribute_block`.\n\nThe engine refuses this \
                 source as a whole: the source is not a list of declarations: an attribute block \
                 cannot stand where a declaration is expected"
            )),
            "a tile of a source refused whole answers its rule and the refusal"
        );
    }

    /// An import answers the file it reads, or why it reads none: a path the
    /// closure reads, with what the file writes of itself, a path naming no
    /// file, and an address with a scheme.
    #[test]
    fn an_import_hovers_the_file_it_reads_1203()
    {
        let corpus = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
        let at = |path: &std::path::Path, written: &str, needle: &str| {
            let text = SourceText::from(written);
            let index = LineIndex::new(written.into());
            let offset = written.find(needle).expect("the import is written");
            let position = Position::of_byte(&index, RenderOffset::from(offset))
                .expect("the needle is on a boundary");
            let session = checked(text);
            let shown = hover(
                text,
                &session,
                &Reading::of(text),
                &hovering(text, path, &session, &gandr_surface_dispatcher::Unshadowed),
                position,
                PLAIN,
            );
            match shown {
                Maybe::Present(shown) => shown.contents.value,
                Maybe::Absent(reason) => panic!("the import hovers nothing: {reason:?}"),
            }
        };
        let importer = corpus.join("model/identity/circle-elim.gandr");
        let written = std::fs::read_to_string(&importer).expect("the importer is read");
        let line = written
            .lines()
            .find(|line| line.starts_with("import "))
            .expect("the importer imports");
        let base =
            gandr_surface_dispatcher::named_path(&corpus.join("model/identity/circle-base.gandr"));
        assert_eq!(
            at(&importer, &written, "circle-base"),
            format!(
                "{}\n\nReads `{}`.\n\n{CIRCLE_BASE}",
                fenced(SourceText::from(line)),
                base.display()
            ),
            "a path the closure reads answers its file and the file's own documentation"
        );
        let missing = written.replacen("circle-base", "circle-nowhere", 1);
        let nowhere = gandr_surface_dispatcher::named_path(
            &corpus.join("model/identity/circle-nowhere.gandr"),
        );
        assert!(
            at(&importer, &missing, "import")
                .ends_with(&format!("No file at `{}`.", nowhere.display())),
            "a path naming no file says so"
        );
        let foreign = corpus.join("surface/module-import.gandr");
        let written = std::fs::read_to_string(&foreign).expect("the importer is read");
        let shown = at(&foreign, &written, "prelude");
        assert!(
            shown.ends_with(
                "An address with a scheme resolves to nothing yet. The tracking issue for this is: \
                 [#1233]\n\n[#1233]: https://github.com/gandr-lang/gandr/issues/1233"
            ),
            "an address with a scheme names its tracking issue: {shown}"
        );
    }

    /// What `circle-base.gandr` writes of itself, as its `//!` lines read.
    const CIRCLE_BASE: &str = "The identity subject's shared declarations, written once and \
                               imported by\nevery source that reads them (`import \
                               \"./circle-base.gandr\" ;`): the empty\ntype, the circle, the \
                               presented integers and the free naturals, the\nwinding number \
                               and spinning with their round trips (the book's § 8.1), and\nthe \
                               maps out of the circle the circle sources state their laws over, \
                               after\ncubical Agda's `Cubical/HITs/S1/Base.agda`. \
                               `circle.gandr` states the\nequivalence `winding` the round trips \
                               make and what it computes; this\nsource states only what the \
                               others read.";

    /// #1365: a position in a source's own `//!` run answers the file and what
    /// it writes of itself, about the run; a word in an ordinary comment still
    /// answers nothing.
    #[test]
    fn a_source_s_own_documentation_hovers_at_its_head_1365()
    {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/identity/circle-base.gandr");
        let written = std::fs::read_to_string(&path).expect("the source is read");
        let text = SourceText::from(written.as_str());
        let session = checked(text);
        let shown = |line: u32, character: u32| match hover(
            text,
            &session,
            &Reading::of(text),
            &hovering(text, &path, &session, &gandr_surface_dispatcher::Unshadowed),
            Position {
                line: Line::from(line),
                character: Character::from(character),
            },
            PLAIN,
        ) {
            Maybe::Present(shown) => Ok((shown.contents.value, shown.range)),
            Maybe::Absent(reason) => Err(reason),
        };
        let (value, range) = shown(3_u32, 10_u32).expect("the run hovers");
        assert_eq!(
            value,
            format!(
                "{}\n\n{CIRCLE_BASE}",
                fenced(SourceText::from("circle-base.gandr"))
            ),
            "the run answers the file and its own documentation"
        );
        assert_eq!(
            (range.start.line, range.end.line),
            (Line::from(0_u32), Line::from(7_u32)),
            "about the whole run"
        );
        let commented = "// A plain comment.\ndef x = 1 ;\n";
        assert_eq!(
            shown_at(SourceText::from(commented), Position {
                line: Line::from(0_u32),
                character: Character::from(5_u32),
            }),
            Err(hovered::Absent::Untyped),
            "an ordinary comment answers nothing"
        );
    }

    /// A source's run target answers as a declaration the outline holds: a
    /// node over its whole form with the target and the thunk type the
    /// checker gave it, each tile inside it by its own entry, its `;` as the
    /// target. A stray answers its refusal at every tile, and so does a run
    /// target the lowering refused, at its attributes (#2073).
    #[test]
    fn a_run_target_and_a_stray_hover_as_declarations_2073()
    {
        let rows: [(&str, &str, String); 7] = [
            (
                "the run target's call",
                "def answer = 42 ;\ndef same(a : Type, x : a) -> -F a { return x }\nsame$0(Integer, answer) ;\n",
                fenced(SourceText::from("same(Integer, answer) : +U (-F Integer)")),
            ),
            (
                "the run target's `;`",
                "def answer = 42 ;\ndef same(a : Type, x : a) -> -F a { return x }\nsame(Integer, answer) $0;\n",
                fenced(SourceText::from("same(Integer, answer) : +U (-F Integer)")),
            ),
            (
                "a name inside the run target",
                "def answer = 42 ;\ndef same(a : Type, x : a) -> -F a { return x }\n$0same(Integer, answer) ;\n",
                fenced(SourceText::from("same : +U ((a : Type) -> a -> -F a)")),
            ),
            (
                "an argument inside the run target",
                "def answer = 42 ;\ndef same(a : Type, x : a) -> -F a { return x }\nsame(Integer, $0answer) ;\n",
                fenced(SourceText::from("answer : Integer")),
            ),
            (
                "a stray",
                "$01 ;\ndef answer = 42 ;\n",
                format!(
                    "{}\n\nrefused: `number`, read as a declaration, is not a former of this sort",
                    fenced(SourceText::from("1"))
                ),
            ),
            (
                "a stray's `;`",
                "1 $0;\ndef answer = 42 ;\n",
                format!(
                    "{}\n\nrefused: `number`, read as a declaration, is not a former of this sort",
                    fenced(SourceText::from("1"))
                ),
            ),
            (
                "the attribute of a refused run target",
                "@[ $0runs ]\nsame(Integer, 1)\n",
                format!(
                    "{}\n\nrefused: `runs` takes a text payload and was given none",
                    fenced(SourceText::from("same(Integer, 1)"))
                ),
            ),
        ];
        for (what, fixture, expected) in rows {
            let (text, position) = marker(SourceText::from(fixture));
            assert_eq!(
                shown_at(SourceText::from(text.as_str()), position),
                Ok(expected),
                "{what}"
            );
        }
    }

    /// The sweep over every tile of the corpus. A hover finds its entry by a
    /// scan of the table, which the enforcing build scans again for each
    /// specification, so a run visits the sources [`Sweep::visit`] names:
    /// under a pull-request profile, plain or enforcing, the sample below and
    /// every source the change adds or modifies; under `sweeps` and `nightly`,
    /// every source. Each visited source hovers every tile.
    mod sweeps
    {
        use gandr_surface_render_remote::ByteOffset as RenderOffset;
        use gandr_surface_render_remote::LineIndex;
        use gandr_surface_syntax::SourceText;
        use gandr_workflow_sweep::Nights;
        use gandr_workflow_sweep::Sample;
        use gandr_workflow_sweep::SampleName;
        use gandr_workflow_sweep::SampleSize;
        use gandr_workflow_sweep::Sweep;
        use gandr_workflow_sweep::corpus;
        use quenchant_shape::shape::Maybe;

        use super::super::UNTYPED;
        use super::super::hover;
        use super::super::hovering;
        use super::PLAIN;
        use super::checked;
        use crate::position::Position;
        use crate::reading::Reading;

        /// The sample: forty-eight sources, ranked by their BLAKE3 digest under
        /// this name, at least one of each corpus class, and every source the
        /// change adds or modifies (`gandr-workflow-sweep`).
        const SAMPLE: Sample = Sample {
            name: SampleName("every_corpus_tile_hovers_or_names_its_issue_1206"),
            size: SampleSize(48),
        };

        /// The nights the nightly profile takes to hover every source's tiles:
        /// half a night. The whole corpus hovered for 44 s to 60 s on the
        /// nightly runner.
        const NIGHTS: Nights = Nights(2);

        /// No tile of the corpus hovers nothing, and none outside a refusal is
        /// one the engine typed nothing at.
        #[test]
        fn every_corpus_tile_hovers_or_names_its_issue_1206()
        {
            let sweep = Sweep::asked().expect("the run's sweep resolves");
            eprintln!("{}", sweep.rotation());
            let sources = sweep.visit_rotating(
                SAMPLE,
                NIGHTS,
                &corpus::sources().expect("the corpus reads"),
            );
            assert!(
                sources.len() >= SAMPLE.size.0,
                "the sample is drawn: {}",
                sources.len()
            );
            let mut silent = Vec::new();
            let mut untyped = Vec::new();
            for source in sources {
                let path = &source.path;
                let written = std::fs::read_to_string(path).expect("a corpus source is read");
                let text = SourceText::from(written.as_str());
                let session = checked(text);
                let reading = Reading::of(text);
                let hovering =
                    hovering(text, path, &session, &gandr_surface_dispatcher::Unshadowed);
                let index = LineIndex::new(written.as_str().into());
                if matches!(reading.declarations(), Maybe::Absent(_)) {
                    silent.push(format!("{}: unread", source.name));
                    continue;
                }
                for tile in reading.tiles() {
                    let start = usize::from(tile.span.start());
                    let position = Position::of_byte(&index, RenderOffset::from(start))
                        .expect("a tile starts on a boundary");
                    let spelled = written
                        .get(start .. usize::from(tile.span.end()))
                        .unwrap_or_default();
                    let line = written
                        .get(.. start)
                        .unwrap_or_default()
                        .matches('\n')
                        .count();
                    let at = format!("{}:{} `{spelled}`", source.name, line.saturating_add(1));
                    match hover(text, &session, &reading, &hovering, position, PLAIN) {
                        Maybe::Absent(reason) => silent.push(format!("{at}: {reason:?}")),
                        Maybe::Present(shown) if shown.contents.value.ends_with(UNTYPED) => {
                            untyped.push(at);
                        },
                        Maybe::Present(_) => {},
                    }
                }
            }
            assert!(
                silent.is_empty(),
                "{} tiles hover nothing:\n{}",
                silent.len(),
                silent.join("\n")
            );
            assert!(
                untyped.is_empty(),
                "{} tiles are typed nothing at outside a refusal:\n{}",
                untyped.len(),
                untyped.join("\n")
            );
        }
    }
}
