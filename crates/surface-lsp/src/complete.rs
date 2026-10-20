//! Completion: the names and keywords the word at a cursor may complete to.
//!
//! A completion request reads the slot where the word at the cursor starts
//! from the parser's continuations of the text before that word
//! ([`Labeled::slot`]): what may be written there, and so which names and
//! keywords may stand. A binding name's slot — after `def`, in a pattern's
//! binder — offers nothing. Where something may be written, the request
//! offers, each once and each starting with the word's prefix:
//!
//! | Slot | Binders in scope | Declared names | Keywords |
//! | --- | --- | --- | --- |
//! | value, computation | each | values and constructors | the forms of an expression |
//! | type | each | families | the forms of a type |
//! | pattern | none | constructors | the forms of a pattern |
//! | item, member, instantiation | none | none | the forms of the sort |
//!
//! The binders are the lowering's: those a name written where the word
//! starts would resolve to, innermost first, a declaration the lowering
//! refused included ([`TypeTable::binders_at`]); an inner binder hides a
//! declaration of its name. The declared names are every declaration of the
//! document's import closure and every constructor its families write, read
//! once per text into [`Names`], a list sorted by name that a prefix cuts by
//! binary search. The keywords are the opening words of the forms the grammar
//! offers the slot's sort, read once per grammar.
//!
//! The list is complete for the prefix: a longer prefix offers a subset of
//! it, so a client filtering as the author types never asks again.
//!
//! Each item carries what it is in the list itself, so a reader sees the types
//! before choosing: a binder its type, read off the table at its written name,
//! and a declared name its head ([`Signatures`]), as the item's detail and, to
//! a client that shows them, beside its label. A resolution adds the
//! documentation.
//!
//! [`Signatures`]: crate::signature::Signatures
//!
//! [`TypeTable::binders_at`]: gandr_surface_dispatcher::TypeTable::binders_at

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::NameKind;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::Subject;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_grammar::Pbg;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Style;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::hover::Hovering;
use crate::inline::Category;
use crate::inline::Forms;
use crate::inline::Labeled;
use crate::inline::Slot;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::CompletionData;
use crate::protocol::CompletionItem;
use crate::protocol::CompletionItemKind;
use crate::protocol::CompletionList;
use crate::protocol::DocumentUri;
use crate::protocol::LabelDetails;
use crate::protocol::LabelsDetailed;
use crate::protocol::MarkupContent;
use crate::protocol::TextEdit;

/// The page width a binder's type is laid out at in a completion: wide enough
/// that a type a reader would write on one line stays on it.
const DETAIL_WIDTH: u32 = 1_000;

/// The names a text's import closure declares, a family's constructors
/// included, each with where it is declared, sorted by name: what a completion
/// cuts a prefix from and what a resolution looks an offered name up in.
///
/// # Specification
/// - requires: built by [`Names::of`].
/// - ensures: ascending by name, then by kind; no name and kind twice.
/// - panics: none.
/// - executable: none — a carrier; [`Names::of`] and [`Names::starting`] carry
///   the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Names::starting`].
/// - witness: `complete::tests::a_prefix_offers_only_what_starts_with_it`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Names(Vec<(String, NameKind, Referent)>);

impl Names
{
    /// The names `table`'s unit declares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each of [`TypeTable::declared_names`] spelled from its
    ///   source's text, with its kind and its referent, ascending by name then
    ///   kind, a name and kind declared twice kept once, at the referent
    ///   [`TypeTable::declared_names`] orders first; a name its source's text
    ///   does not hold is dropped.
    /// - provides: the index a completion request reads, built once per text.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the declared names and one sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling's names complete in an importer, and a
    ///   prefix cuts exactly the names starting with it.
    /// - witness: `complete::tests::a_prefix_offers_only_what_starts_with_it`
    /// - witness: `tests::session::a_completion_offers_what_a_sibling_declares_806`
    #[spec(ensures: |ret| ret.0.windows(2).all(|pair| matches!(pair, [first, second] if (&first.0, first.1) < (&second.0, second.1))))]
    #[must_use]
    pub fn of(table: &TypeTable) -> Self
    {
        let mut names: Vec<(String, NameKind, Referent)> = table
            .declared_names()
            .iter()
            .filter_map(|&(referent, kind)| {
                let named = referent.named();
                let text = <&str>::from(table.source_text(referent.source())?);
                let name = text.get(usize::from(named.start()) .. usize::from(named.end()))?;
                Some((String::from(name), kind, referent))
            })
            .collect();
        names.sort_unstable();
        names.dedup_by(|second, first| first.0 == second.0 && first.1 == second.1);
        Self(names)
    }

    /// Where `name`, offered as `kind`, is declared.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the referent kept for `name` and `kind`, none when the
    ///   closure declares no such name.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one binary search.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a resolved function, constructor and family each read
    ///   their own head; a name the text no longer declares resolves to
    ///   nothing.
    /// - witness: `complete::tests::a_resolved_name_reads_its_head_and_documentation`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the check walks the names once, as building them cost"
        )
    )]
    #[spec(ensures: |ret| ret.is_none_or(|found| self.0.iter().any(|&(ref held, as_kind, referent)| held.as_str() == <&str>::from(name) && as_kind == kind && referent == found)))]
    fn declared(
        &self,
        name: SourceText<'_>,
        kind: NameKind,
    ) -> Option<Referent>
    {
        let key = (<&str>::from(name), kind);
        self.0
            .binary_search_by(|&(ref held, as_kind, _)| (held.as_str(), as_kind).cmp(&key))
            .ok()
            .and_then(|at| self.0.get(at))
            .map(|&(_, _, referent)| referent)
    }

    /// The names starting with `prefix`, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the entries whose name starts with `prefix`, in
    ///   order; every entry for the empty prefix.
    /// - fails: never.
    /// - panics: none.
    /// - intension: two binary searches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `de` offers the names starting with `de` and no
    ///   other; a cut by linear scan or by substring changes it.
    /// - witness: `complete::tests::a_prefix_offers_only_what_starts_with_it`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the check walks the names once, as building them cost"
        )
    )]
    #[spec(ensures: |ret| ret.len() == self.0.iter().filter(|&&(ref name, _, _)| name.starts_with(<&str>::from(prefix))).count()
        && ret.iter().all(|&(ref name, _, _)| name.starts_with(<&str>::from(prefix))))]
    fn starting(
        &self,
        prefix: SourceText<'_>,
    ) -> &[(String, NameKind, Referent)]
    {
        let prefix = <&str>::from(prefix);
        let first = self
            .0
            .partition_point(|&(ref name, ..)| name.as_str() < prefix);
        let rest = self.0.get(first ..).unwrap_or_default();
        let taken = rest.partition_point(|&(ref name, ..)| name.starts_with(prefix));
        rest.get(.. taken).unwrap_or_default()
    }
}

/// How a slot of `category` offers a declared name of `kind`: as the
/// protocol's kind for it, or not at all.
///
/// # Specification
/// - ensures: a value or a computation offers values as functions and
///   constructors as constructors; a type offers families as enums; a pattern
///   offers constructors; nothing else offers a declared name.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the slot witness offers a family in a type, a constructor
///   in a pattern and a function in a body, each nowhere else.
/// - witness: `complete::tests::each_slot_offers_its_own_names`
#[spec(ensures: |ret| ret.is_none() || !matches!(category, Category::Item | Category::Member | Category::Instantiation))]
const fn offered_as(
    category: Category,
    kind: NameKind,
) -> Option<CompletionItemKind>
{
    match (category, kind) {
        (Category::Value | Category::Computation, NameKind::Value) => {
            Some(CompletionItemKind::FUNCTION)
        },
        (Category::Value | Category::Computation | Category::Pattern, NameKind::Constructor) => {
            Some(CompletionItemKind::CONSTRUCTOR)
        },
        (Category::Type, NameKind::Family) => Some(CompletionItemKind::ENUM),
        _ => None,
    }
}

/// What a declared name offered as `kind` names: the inverse of
/// [`offered_as`].
///
/// # Specification
/// trivial.
const fn declared_as(kind: CompletionItemKind) -> Option<NameKind>
{
    match kind {
        CompletionItemKind::FUNCTION => Some(NameKind::Value),
        CompletionItemKind::CONSTRUCTOR => Some(NameKind::Constructor),
        CompletionItemKind::ENUM => Some(NameKind::Family),
        _ => None,
    }
}

/// The completions at `position` of `text`, the document at `uri` whose copy
/// keeps `hovering`, under `grammar` whose forms are `forms`, each type spelled
/// in `printer`'s style and label details given when `labels` says the client
/// shows them.
///
/// # Specification
/// - requires: `hovering` was read off `text`; `forms` is [`Forms::new`] of
///   `grammar`.
/// - ensures: a complete list. Where the word ending at the position's byte
///   starts — the position itself when no word ends there — the slot
///   [`Labeled::slot`] reads in the text before it; for an open slot, the names
///   and keywords the module's table states for its category that start with
///   the word's text up to the position, each once and each written over that
///   text: the binders in scope where the word starts, innermost first, then
///   the declared names the slot admits, by name, then the keywords, in mold
///   order; a name a binder already offers is not offered again. Each item's
///   sort text is its position, so the client keeps this order, and each
///   declared name carries `uri` for its resolution. A binder the table types
///   at its written name carries `name : type` as its detail; a declared name
///   whose head [`Signatures`] keeps carries that head's label, unless it is
///   the name alone; a keyword carries none. When `labels` holds, an item with
///   a detail carries it beside its label too: the rest after the name when the
///   detail starts with it, the detail whole as the description otherwise. No
///   item for a filled slot.
/// - provides: the answer to `textDocument/completion` for a held document.
/// - fails: never.
/// - panics: none.
/// - intension: one relabeling and one molding of the form the word's start
///   ends, a walk of the binders in scope with one table lookup each, two
///   binary searches of the names and one of the heads per declared name.
///
/// # Adequacy
/// - hypothesis: L3 — a value, a computation, a type, a pattern, an item and a
///   binding name's slot each offer their exact names; a prefix offers only
///   what starts with it; a binder offers in its arm and not in its sibling,
///   inside a declaration the lowering refused; a sibling's declaration offers
///   in an importer; a binder, a function, a constructor, a family and a value
///   whose head is its name alone carry their exact details, with and without
///   label details.
/// - witness: `complete::tests::each_slot_offers_its_own_names`
/// - witness: `complete::tests::a_prefix_offers_only_what_starts_with_it`
/// - witness: `complete::tests::a_binder_offers_only_where_it_is_in_scope_806`
/// - witness: `complete::tests::each_item_carries_its_type_in_the_list`
/// - witness: `tests::session::a_completion_offers_what_a_sibling_declares_806`
///
/// [`Signatures`]: crate::signature::Signatures
#[spec(ensures: |ret| !ret.is_incomplete && ret.items.iter().all(|item| item.text_edit.range.end == position
    && item.label_details.is_some() == (labels.0 && item.detail.is_some())))]
#[must_use]
pub fn completions(
    grammar: &Pbg,
    forms: &Forms,
    text: SourceText<'_>,
    hovering: &Hovering,
    (uri, position): (&DocumentUri, Position),
    (printer, labels): (Style, LabelsDetailed),
) -> CompletionList
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = position.byte(&index);
    let whole = Labeled::new(text);
    let start = whole.cut(at).word_start();
    let prefix = <&str>::from(text)
        .get(usize::from(start) .. usize::from(at))
        .unwrap_or_default();
    let range = Range::of_bytes(&index, start, at).unwrap_or(Range {
        start: position,
        end: position,
    });
    let Slot::Open(category) = whole.cut(start).slot(grammar)
    else {
        return CompletionList {
            is_incomplete: false,
            items: Vec::new(),
        };
    };
    let table = hovering.table();
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut offered: Vec<(&str, CompletionItemKind, Option<String>)> = Vec::new();
    if matches!(
        category,
        Category::Value | Category::Computation | Category::Type
    ) {
        for (binder, site) in table.binders_at(ByteOffset::from(usize::from(start))) {
            let name = <&str>::from(binder);
            if name.starts_with(prefix) && seen.insert(name) {
                let typed = match table.at(site.start(), PageWidth::from(DETAIL_WIDTH), printer) {
                    Maybe::Present(entry)
                        if entry.span() == site && entry.subject() == Subject::Binder =>
                    {
                        Some(format!("{name} : {}", entry.ty().as_ref()))
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => None,
                };
                offered.push((name, CompletionItemKind::VARIABLE, typed));
            }
        }
    }
    for &(ref name, kind, ref referent) in hovering.names().starting(SourceText::from(prefix)) {
        if let Some(as_kind) = offered_as(category, kind)
            && seen.insert(name.as_str())
        {
            let head = hovering
                .signatures()
                .declared(referent)
                .map(|signature| <&str>::from(signature.label()))
                .filter(|head| *head != name.as_str())
                .map(String::from);
            offered.push((name.as_str(), as_kind, head));
        }
    }
    for keyword in forms.keywords(category) {
        if keyword.starts_with(prefix) && seen.insert(keyword) {
            offered.push((keyword, CompletionItemKind::KEYWORD, None));
        }
    }
    let width = offered.len().to_string().len();
    CompletionList {
        is_incomplete: false,
        items: offered
            .into_iter()
            .enumerate()
            .map(|(rank, (name, kind, head))| CompletionItem {
                label: String::from(name),
                kind,
                sort_text: format!("{rank:0width$}"),
                text_edit: TextEdit {
                    range,
                    new_text: String::from(name),
                },
                label_details: head
                    .as_deref()
                    .filter(|_| labels.0)
                    .map(|head| beside(SourceText::from(name), SourceText::from(head))),
                detail: head,
                documentation: None,
                data: declared_as(kind).map(|_| CompletionData { uri: uri.clone() }),
            })
            .collect(),
    }
}

/// What a client shows beside the label `name` of an item whose detail is
/// `head`: the rest of the head right after the label when the head starts with
/// the name, the head whole apart from it otherwise.
///
/// # Specification
/// trivial.
fn beside(
    name: SourceText<'_>,
    head: SourceText<'_>,
) -> LabelDetails
{
    <&str>::from(head)
        .strip_prefix(<&str>::from(name))
        .map_or_else(
            || LabelDetails {
                detail: None,
                description: Some(String::from(<&str>::from(head))),
            },
            |rest| LabelDetails {
                detail: Some(String::from(rest)),
                description: None,
            },
        )
}

/// `item`, offered off the text whose copy keeps `hovering`, resolved: a
/// declared name's head, when it writes more than the name, as its detail, and
/// the documentation written for it, as markdown.
///
/// # Specification
/// - requires: `hovering` was read off the text `item` was offered in, or a
///   later text of the same document.
/// - ensures: for a function, a constructor or a family whose name and kind the
///   closure still declares and whose head [`Signatures`] keeps, the item with
///   that head's label as its detail unless it is the name alone, and that
///   head's documentation as markdown; every other item, a binder's and a
///   keyword's among them, unchanged. The label, kind, sort text, edit and data
///   are unchanged.
/// - provides: the answer to `completionItem/resolve`.
/// - fails: never.
/// - panics: none.
/// - intension: one binary search of the names and one of the heads.
///
/// # Adequacy
/// - hypothesis: L3 — a documented function with parameters, a constructor with
///   fields, a family, a value whose head is its name alone, a binder, a
///   keyword and a name no longer declared are each resolved to their exact
///   detail and documentation.
/// - witness: `complete::tests::a_resolved_name_reads_its_head_and_documentation`
///
/// [`Signatures`]: crate::signature::Signatures
#[spec(
    captures: before = item.clone(),
    ensures: |ret| ret.label == before.label && ret.kind == before.kind
        && ret.sort_text == before.sort_text && ret.text_edit == before.text_edit && ret.data == before.data,
)]
#[must_use]
pub fn resolved(
    mut item: CompletionItem,
    hovering: &Hovering,
) -> CompletionItem
{
    let Some(signature) = declared_as(item.kind)
        .and_then(|kind| {
            hovering
                .names()
                .declared(SourceText::from(item.label.as_str()), kind)
        })
        .and_then(|referent| hovering.signatures().declared(&referent))
    else {
        return item;
    };
    let label = <&str>::from(signature.label());
    if label != item.label {
        item.detail = Some(String::from(label));
    }
    item.documentation = signature.documentation().map(|written| MarkupContent {
        kind: "markdown",
        value: String::from(<&str>::from(written)),
    });
    item
}

#[cfg(test)]
mod tests
{
    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_render_remote::ByteOffset as RenderOffset;
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_session::Session;
    use gandr_surface_syntax::SourceText;

    use super::completions;
    use super::resolved;
    use crate::hover::Hovering;
    use crate::hover::hovering;
    use crate::position::Position;
    use crate::protocol::CompletionItem;
    use crate::protocol::CompletionItemKind;
    use crate::protocol::DocumentUri;
    use crate::protocol::LabelsDetailed;
    use crate::protocol::TextEdit;
    use crate::recheck::forms;
    use crate::recheck::grammar;

    /// A family, a recursive function matching on it, and a function whose
    /// body is a lambda.
    const BASE: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec \
                        plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    \
                        Succ(p) => Succ(plus[<](n, p))\n  }\n}\ndef double : +U (Nat -> -F \
                        Nat) ;\ndef double = thunk { fn (x) { return x } } ;\n";

    /// What a completion offers: each name with its kind, and each keyword,
    /// in order.
    #[derive(Debug, Default)]
    struct Offered
    {
        /// The binders and the declared names.
        names: Vec<(String, CompletionItemKind)>,
        /// The keywords.
        keywords: Vec<String>,
    }

    /// What a session judging `source` keeps for its hovers.
    ///
    /// # Specification
    /// trivial.
    fn hovered(source: SourceText<'_>) -> Hovering
    {
        let mut session = Session::new(
            grammar().expect("the grammar builds").clone(),
            SourceRoot::Strict,
            MemoryCheckpointStore::default(),
            InMemoryBlockStore::default(),
            BackendArtifact::from(b"complete".as_slice()),
        );
        let _judged = session.judge(source).expect("the session does not fault");
        hovering(
            source,
            std::path::Path::new(""),
            &session,
            &gandr_surface_dispatcher::Unshadowed,
        )
    }

    /// The list a completion answers in `before` followed by `after`, at the
    /// end of `before`, to a client that shows label details when `labels`
    /// holds.
    ///
    /// # Specification
    /// trivial.
    fn listed(
        before: SourceText<'_>,
        after: SourceText<'_>,
        labels: LabelsDetailed,
    ) -> Vec<CompletionItem>
    {
        let text = format!("{}{}", <&str>::from(before), <&str>::from(after));
        let source = SourceText::from(text.as_str());
        let index = LineIndex::new(text.as_str().into());
        let position = Position::of_byte(&index, RenderOffset::from(<&str>::from(before).len()))
            .expect("the cursor is in the text");
        completions(
            grammar().expect("the grammar builds"),
            forms().expect("the forms build"),
            source,
            &hovered(source),
            (&DocumentUri::from("file:///complete.gandr"), position),
            (
                gandr_surface_pretty::Style {
                    form: gandr_surface_pretty::Form::Sugared,
                    spelling: gandr_surface_pretty::Spelling::Unicode,
                },
                labels,
            ),
        )
        .items
    }

    /// What a completion offers in `before` followed by `after`, at the end
    /// of `before`.
    ///
    /// # Specification
    /// trivial.
    fn offered(
        before: SourceText<'_>,
        after: SourceText<'_>,
    ) -> Offered
    {
        let mut offered = Offered::default();
        for item in listed(before, after, LabelsDetailed(false)) {
            if item.kind == CompletionItemKind::KEYWORD {
                offered.keywords.push(item.label);
            }
            else {
                offered.names.push((item.label, item.kind));
            }
        }
        offered
    }

    /// [`BASE`] cut where `marker` first occurs.
    ///
    /// # Specification
    /// trivial.
    fn cut(marker: SourceText<'_>) -> (SourceText<'static>, SourceText<'static>)
    {
        let at = BASE.find(<&str>::from(marker)).expect("the marker occurs");
        (
            SourceText::from(BASE.get(.. at).unwrap_or_default()),
            SourceText::from(BASE.get(at ..).unwrap_or_default()),
        )
    }

    /// `names` with their kinds, as [`Offered::names`] holds them.
    macro_rules! named {
        ($names:expr) => {
            $names
                .into_iter()
                .map(|(name, kind): (&str, CompletionItemKind)| (String::from(name), kind))
                .collect::<Vec<(String, CompletionItemKind)>>()
        };
    }

    #[test]
    fn each_slot_offers_its_own_names()
    {
        use CompletionItemKind as Kind;

        let at = |marker: &'static str| {
            let (before, after) = cut(SourceText::from(marker));
            offered(before, after)
        };
        let has = |offered: &Offered, keyword: &str| {
            offered.keywords.iter().any(|written| written == keyword)
        };

        let value = at("p))");
        assert_eq!(
            value.names,
            named!([
                ("p", Kind::VARIABLE),
                ("m", Kind::VARIABLE),
                ("plus", Kind::VARIABLE),
                ("n", Kind::VARIABLE),
                ("Succ", Kind::CONSTRUCTOR),
                ("Zero", Kind::CONSTRUCTOR),
                ("double", Kind::FUNCTION),
            ]),
            "a value: the binders in scope, innermost first, then the values and constructors"
        );
        assert!(
            has(&value, "thunk") && !has(&value, "def") && !has(&value, "Type"),
            "{value:?}"
        );

        let computation = at("case m");
        assert_eq!(
            computation.names,
            named!([
                ("m", Kind::VARIABLE),
                ("plus", Kind::VARIABLE),
                ("n", Kind::VARIABLE),
                ("Succ", Kind::CONSTRUCTOR),
                ("Zero", Kind::CONSTRUCTOR),
                ("double", Kind::FUNCTION),
            ]),
            "a body: the parameters, never a pattern's binder"
        );
        assert!(
            has(&computation, "return") && has(&computation, "case"),
            "{computation:?}"
        );

        let ty = at("Nat) ;");
        assert_eq!(
            ty.names,
            named!([("Nat", Kind::ENUM)]),
            "a type: the families alone"
        );
        assert!(has(&ty, "Type") && !has(&ty, "return"), "{ty:?}");

        let pattern = at("Zero =>");
        assert_eq!(
            pattern.names,
            named!([("Succ", Kind::CONSTRUCTOR), ("Zero", Kind::CONSTRUCTOR)]),
            "a pattern: the constructors alone"
        );
        assert!(!has(&pattern, "return"), "{pattern:?}");

        let item = at("def double =");
        assert!(item.names.is_empty(), "an item: no name, {item:?}");
        assert!(
            has(&item, "def") && has(&item, "data") && !has(&item, "return"),
            "{item:?}"
        );

        let binding = at("plus(n");
        assert!(
            binding.names.is_empty() && binding.keywords.is_empty(),
            "a binding name: nothing, {binding:?}"
        );
    }

    #[test]
    fn a_prefix_offers_only_what_starts_with_it()
    {
        use CompletionItemKind as Kind;

        let typed = format!("{BASE}de");
        let item = offered(SourceText::from(typed.as_str()), SourceText::from(""));
        assert!(item.names.is_empty(), "{item:?}");
        assert_eq!(item.keywords, ["def"], "an item's `de`: the keyword alone");

        let (before, after) = cut(SourceText::from("x } }"));
        let typed = format!("{}d", <&str>::from(before));
        let value = offered(
            SourceText::from(typed.as_str()),
            SourceText::from(<&str>::from(after).get(1 ..).unwrap_or_default()),
        );
        assert_eq!(
            value.names,
            named!([("double", Kind::FUNCTION)]),
            "a value's `d`: the names starting with it"
        );
        assert!(
            !value.keywords.is_empty()
                && value
                    .keywords
                    .iter()
                    .all(|keyword| keyword.starts_with('d')),
            "a value's `d`: the keywords starting with it, {value:?}"
        );
    }

    /// #806: a pattern's binder offers in its own arm and not in its sibling,
    /// though the lowering refuses the declaration being typed.
    #[test]
    fn a_binder_offers_only_where_it_is_in_scope_806()
    {
        use CompletionItemKind as Kind;

        let head = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec plus(n : \
                    Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => ";
        let own = format!("{head}n,\n    Succ(p) => Succ(p");
        let own = offered(
            SourceText::from(own.as_str()),
            SourceText::from(")\n  }\n}\n"),
        );
        assert_eq!(
            own.names,
            named!([("p", Kind::VARIABLE), ("plus", Kind::VARIABLE)]),
            "in its arm: the pattern's binder, then the recursion"
        );
        let sibling = format!("{head}p");
        let sibling = offered(
            SourceText::from(sibling.as_str()),
            SourceText::from(",\n    Succ(p) => Succ(p)\n  }\n}\n"),
        );
        assert_eq!(
            sibling.names,
            named!([("plus", Kind::VARIABLE)]),
            "in the sibling arm: the recursion alone"
        );
    }

    #[test]
    fn each_item_carries_its_type_in_the_list()
    {
        let details = |before: &str, after: &str, labels: LabelsDetailed| {
            listed(SourceText::from(before), SourceText::from(after), labels)
                .into_iter()
                .filter(|item| item.kind != CompletionItemKind::KEYWORD)
                .map(|item| {
                    (
                        item.label,
                        item.detail,
                        item.label_details
                            .map(|beside| (beside.detail, beside.description)),
                    )
                })
                .collect::<Vec<_>>()
        };
        let at = |marker: &str, labels: LabelsDetailed| {
            let (before, after) = cut(SourceText::from(marker));
            details(<&str>::from(before), <&str>::from(after), labels)
        };
        let shown = |text: &str| Some(String::from(text));
        assert_eq!(
            at("))\n  }\n}", LabelsDetailed(true)),
            [
                (
                    String::from("p"),
                    shown("p : Nat"),
                    Some((shown(" : Nat"), None))
                ),
                (
                    String::from("plus"),
                    shown("plus : Nat => Nat"),
                    Some((shown(" : Nat => Nat"), None))
                ),
            ],
            "a binder carries its type, in the list and beside its label"
        );
        assert_eq!(
            at("cc(plus", LabelsDetailed(true)),
            [(
                String::from("Succ"),
                shown("Succ : (n : Nat) --> Nat"),
                Some((shown(" : (n : Nat) --> Nat"), None))
            )],
            "a constructor carries its fields"
        );
        assert_eq!(
            details(
                format!("{BASE}def three : -F Nat ;\ndef three = pl").as_str(),
                " ;\n",
                LabelsDetailed(true)
            ),
            [(
                String::from("plus"),
                shown("plus(n : Nat, m : Nat) -> -F Nat"),
                Some((shown("(n : Nat, m : Nat) -> -F Nat"), None))
            )],
            "a function's parameters and result run on after its name"
        );
        assert_eq!(
            details(
                format!("{BASE}def answer = 42 ;\ndef three = ans").as_str(),
                " ;\n",
                LabelsDetailed(true)
            ),
            [(String::from("answer"), None, None)],
            "a value whose head is its name alone carries nothing beside it"
        );
        assert!(
            at("))\n  }\n}", LabelsDetailed(false))
                .iter()
                .all(|&(_, ref detail, ref beside)| detail.is_some() && beside.is_none()),
            "a client that shows no label details is given the detail alone"
        );
    }

    #[test]
    fn a_resolved_name_reads_its_head_and_documentation()
    {
        use CompletionItemKind as Kind;

        let hovering = hovered(SourceText::from(
            "/// Natural numbers.\ndata Nat : Type {\n  Zero : Nat;\n  /// One more.\n  Succ : (n \
             : Nat) --> Nat;\n}\n/// Addition.\ndef rec plus(n : Nat, m : Nat) -> -F Nat {\n  \
             case m {\n    Zero => n,\n    Succ(p) => Succ(plus[<](n, p))\n  }\n}\n/// The \
             answer.\ndef answer = 42 ;\n",
        ));
        let resolve = |label: &str, kind: CompletionItemKind| {
            let item = resolved(
                CompletionItem {
                    label: String::from(label),
                    kind,
                    sort_text: String::from("0"),
                    text_edit: TextEdit {
                        range: crate::position::Range::default(),
                        new_text: String::from(label),
                    },
                    detail: None,
                    label_details: None,
                    documentation: None,
                    data: None,
                },
                &hovering,
            );
            (item.detail, item.documentation.map(|written| written.value))
        };
        let read = |detail: Option<&str>, documentation: Option<&str>| {
            (detail.map(String::from), documentation.map(String::from))
        };
        assert_eq!(
            resolve("plus", Kind::FUNCTION),
            read(Some("plus(n : Nat, m : Nat) -> -F Nat"), Some("Addition.")),
            "a function: its head and its documentation"
        );
        assert_eq!(
            resolve("Succ", Kind::CONSTRUCTOR),
            read(Some("Succ : (n : Nat) --> Nat"), Some("One more.")),
            "a constructor: its fields"
        );
        assert_eq!(
            resolve("Zero", Kind::CONSTRUCTOR),
            read(Some("Zero : Nat"), None),
            "an undocumented constructor: its head alone"
        );
        assert_eq!(
            resolve("Nat", Kind::ENUM),
            read(Some("Nat : Type"), Some("Natural numbers.")),
            "a family"
        );
        assert_eq!(
            resolve("answer", Kind::FUNCTION),
            read(None, Some("The answer.")),
            "a value whose head is its name alone: its documentation"
        );
        assert_eq!(
            resolve("Nat", Kind::FUNCTION),
            read(None, None),
            "a name offered as what it does not name: unchanged"
        );
        assert_eq!(
            resolve("gone", Kind::FUNCTION),
            read(None, None),
            "a name the text does not declare: unchanged"
        );
        assert_eq!(
            resolve("n", Kind::VARIABLE),
            read(None, None),
            "a binder: unchanged"
        );
        assert_eq!(
            resolve("case", Kind::KEYWORD),
            read(None, None),
            "a keyword: unchanged"
        );
    }
}
