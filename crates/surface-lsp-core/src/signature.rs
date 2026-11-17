//! Signature help and the context stack: each spine a position stands in, the
//! declared head of each, and the slot the position fills.
//!
//! A held text's reading keeps the context stack of the text
//! ([`Stack`]): the spines of each form, a juxtaposed application and a
//! family's application alike, which the form store keeps with the form's
//! region. A copy's hovering keeps the head of every declaration and
//! constructor its import closure writes ([`Signatures`]): the name through its
//! parameters and its result on one line, each parameter's place in that label
//! with the `///` run written before it, and the documentation written for the
//! head. The heads are read once per text, off the parse it already makes; the
//! heads the closure writes are read once per closure lowering the process
//! holds and shared by every text laid after it, so a keystroke reads the
//! document's own forms alone. The type table's referent index
//! ([`TypeTable::referent`]) gives the declaration a spine's head refers to.
//! The faces read the spines a position stands in once, from the innermost
//! outward. A position past the last argument of a spine, after layout on its
//! line, opens the spine's next slot while its declared head takes one. A
//! position after a head that has no argument yet, and layout on its line,
//! opens that head's first slot in the same way. So a space typed after a head
//! whose type still takes arguments stands in the slot that it opens.
//! Signature help answers one signature per spine, the innermost active, each
//! with the parameter its slot fills. A `gandr/stack` request answers each
//! spine: its head, the type the judgement gives the head, the declared head
//! and its arity, the slot, and the type the judgement checked the slot's
//! argument against, or none where the judgement typed no term in the slot.
//! The stack card of the render bus holds the same rows, the type of each head
//! with the run its slot's parameter writes. None of them reads text past the
//! layout before the position, or resolves a name.
//!
//! The heads are read off the declaring form of each, as the `signature`
//! module of `gandr-surface-lsp-base` reads them.
//!
//! [`Stack`]: gandr_surface_session::Stack
//! [`TypeTable::referent`]: gandr_surface_dispatcher::TypeTable::referent

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::sync::Mutex;
use std::sync::PoisonError;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypedSpan;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lsp_base::signature::Head;
use gandr_surface_lsp_base::signature::ParameterSlot;
use gandr_surface_lsp_base::signature::Signature;
use gandr_surface_lsp_base::signature::heads_among;
use gandr_surface_lsp_base::signature::parameters_documented;
use gandr_surface_pretty::Style;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::SpineRow;
use gandr_surface_render_remote::StackCard;
use gandr_surface_session::ClosureKey;
use gandr_surface_session::Frame;
use gandr_surface_session::Holding;
use gandr_surface_session::Slot;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::hover::Hovering;
use crate::position::Position;
use crate::position::ranged;
use crate::protocol::Answer;
use crate::protocol::LabelOffsets;
use crate::protocol::SignatureHelp;
use crate::protocol::SignatureInformation;
use crate::protocol::StackRow;
use crate::reading::Reading;

/// The heads each closure lowering's part of a tree writes, by the lowering's
/// key: read the first time a text is laid after the lowering, and let go
/// once nothing holds the lowering.
// economy: no byte form, the codec is #4084. The heads are keyed by the
// lowering they come from, so they cross the store under the lowering's
// content key once the lowering has an image.
static CLOSURE_HEADS: Mutex<Vec<(ClosureKey, Arc<[Head]>)>> = Mutex::new(Vec::new());

/// The heads that an import closure writes, by the source and the name tile of
/// each head.
///
/// A head is a declaration, a constructor or a binder typed by a function. The
/// heads of the closure are shared with every text laid after the same closure
/// lowering, and the document's own text writes the rest.
///
/// # Specification
/// - requires: built by [`Signatures::of`] or [`Signatures::after`].
/// - ensures: each part ascending by source, then name tile, no tile twice;
///   every source of the closure's part before every source of the document's.
/// - panics: none.
/// - executable: none — a carrier; [`Signatures::of`], [`Signatures::after`]
///   and [`Signatures::declared`] carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Signatures::of`] and [`Signatures::after`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `gandr-surface-lsp-diagnostics::tests::signature::a_closure_s_heads_are_read_once_per_lowering_1403`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Signatures
{
    /// The heads the closure a text is laid after writes.
    closure: Arc<[Head]>,
    /// The heads the text's own forms write.
    own: Vec<Head>,
    /// The documentation of each parameter the text's own heads write that
    /// has any, by the source holding the parameter's first tile and that
    /// tile's span in the source's own text, ascending.
    documented: Vec<((SourceIndex, ByteSpan), String)>,
}

impl Signatures
{
    /// The heads `tree`, parsed under `grammar` over the text `unit` lays out
    /// and classified by `roles`, writes, each keyed by the source holding its
    /// name and the name's span in that source's own text.
    ///
    /// # Specification
    /// - requires: `tree` was parsed under `grammar` over the text `unit` lays
    ///   out.
    /// - ensures: one head per tile an item or module member owns that the
    ///   highlighter classifies as a function, a value, a type or a constructor
    ///   being declared, as the base's `signature` table reads it, its
    ///   documentation that of the documentation nodes written before it in its
    ///   form since the last head, else of those written before the form or in
    ///   the attribute blocks before it; then one head per tile any form owns
    ///   or holds that the form's own `:` follows and a function type after it,
    ///   as the table reads it, undocumented; each for a tile `unit` places in
    ///   a source, the first head for a tile kept; all of them the text's own.
    ///   A head laid over lines labels as one line: each stretch of layout that
    ///   breaks a line or holds documentation is one space, none inside its
    ///   parentheses or before a comma. A parameter carries the documentation
    ///   nodes written before it inside its list or telescope, and none of them
    ///   documents the head.
    /// - provides: the index a signature-help request answers from, built once
    ///   per text.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the tree, one pass over each form's children,
    ///   and one sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function with a parameter list, one with a
    ///   signature's arrow, a family with parameters, a constructor with fields
    ///   and one with none, a head over two lines, documented ones, a parameter
    ///   typed by an arrow and record fields typed by an arrow and over a
    ///   telescope each read at their exact label and parameters; documented
    ///   parameters of a list laid over lines and of a telescope, a run of two
    ///   lines among them, at their exact documentation.
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    #[spec(ensures: |ret| ret.closure.is_empty()
        && ret.own.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
    #[must_use]
    #[inline]
    pub fn of(
        grammar: &Pbg,
        roles: &RoleTable,
        tree: &SyntaxTree<'_>,
        unit: &Unit,
    ) -> Self
    {
        let own = heads_among(
            grammar,
            roles,
            tree,
            unit,
            tree.roots().iter().flat_map(|&root| tree.children(root)),
        );
        Self {
            closure: Arc::default(),
            documented: parameters_documented(unit, &own),
            own,
        }
    }

    /// The heads `tree`, the text `unit` lays out with the document's own text
    /// from `base` on, writes, as [`Signatures::of`] reads them: those of the
    /// forms before `base` under the closure's part, and those of the forms
    /// from `base` on under the text's own.
    ///
    /// # Specification
    /// - requires: as [`Signatures::of`]; `tree`'s forms before `base` are the
    ///   closure's, and `closure` names the lowering of them the process holds,
    ///   when it holds one.
    /// - ensures: [`Signatures::of`]'s heads, each top-level form read with the
    ///   documentation written before it on its own side of `base`. When
    ///   `closure` names a lowering, the closure's part is the one kept for it,
    ///   read now when nothing is kept, and kept until nothing holds the
    ///   lowering. Else the closure's part is read now and not kept. The split
    ///   does not depend on whether the process holds the lowering (#5198).
    /// - provides: a keystroke's heads read off the document's own forms alone.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the forms from `base` on, one lock and a scan
    ///   of the kept closures; the closure's forms walked once per lowering, or
    ///   once per call when no lowering is named.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an importer read after its closure's lowering, read
    ///   whole, and read again after an edit of its own text answers the same
    ///   heads, and the second reading finds the closure's part kept; a hover
    ///   read before any lowering of the closure splits the heads as the
    ///   recheck after it does; a hover after a keystroke answers from the
    ///   heads its judgement read, without the copy parsing its text.
    /// - witness: `gandr-surface-lsp-diagnostics::tests::signature::a_closure_s_heads_are_read_once_per_lowering_1403`
    /// - witness: `gandr-surface-lsp-diagnostics::recheck::tests::a_hover_before_its_closure_is_lowered_splits_as_a_recheck_does_5198`
    /// - witness: `gandr-surface-lsp::server::tests::a_hover_reads_the_parse_its_judgement_made_2440`
    #[spec(ensures: |ret| ret.own.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
    #[must_use]
    #[inline]
    pub fn after(
        grammar: &Pbg,
        roles: &RoleTable,
        (tree, unit, base): (&SyntaxTree<'_>, &Unit, ByteOffset),
        closure: Option<&ClosureKey>,
    ) -> Self
    {
        let top = || tree.roots().iter().flat_map(|&root| tree.children(root));
        let before = |child: &NodeIndex| {
            tree.node(*child)
                .is_some_and(|node| node.span().start() < base)
        };
        let own = heads_among(
            grammar,
            roles,
            tree,
            unit,
            top().filter(|child| !before(child)),
        );
        let read = || heads_among(grammar, roles, tree, unit, top().filter(before));
        Self {
            closure: closure
                .map_or_else(|| Arc::from(read()), |closure| closure_heads(closure, read)),
            documented: parameters_documented(unit, &own),
            own,
        }
    }

    /// The head written where `referent` is named.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn declared(
        &self,
        referent: &Referent,
    ) -> Option<&Signature>
    {
        let key = (referent.source(), referent.named());
        [&*self.closure, self.own.as_slice()]
            .into_iter()
            .find_map(|heads| {
                let at = heads.binary_search_by(|held| held.0.cmp(&key)).ok()?;
                heads.get(at)
            })
            .map(|held| &held.1)
    }

    /// The documentation written before the parameter of one of the text's
    /// own heads whose first tile `source` writes at `named`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a documented parameter answers its run at its name
    ///   tile, and a tile no run documents answers nothing.
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `hover::tests::a_documented_parameter_hovers_its_documentation_1116`
    #[must_use]
    #[inline]
    pub fn parameter(
        &self,
        source: SourceIndex,
        named: ByteSpan,
    ) -> Option<SourceText<'_>>
    {
        let key = (source, named);
        let at = self
            .documented
            .binary_search_by(|held| held.0.cmp(&key))
            .ok()?;
        self.documented
            .get(at)
            .map(|held| SourceText::from(held.1.as_str()))
    }
}

/// The heads kept for the closure lowering `key` names, read by `read` and
/// kept when none are, every kept entry whose lowering nothing holds let go.
///
/// # Specification
/// - requires: `read` reads the heads of the closure's part of a tree laid
///   after the lowering `key` names.
/// - ensures: the heads kept for `key` when any are, else `read`'s, kept for
///   `key`.
/// - fails: never.
/// - panics: only by propagating a panic of `read`.
/// - executable: none — the clauses read the process's table, which the call
///   locks inside; the witness observes the second reading find the first's.
///
/// # Adequacy
/// - hypothesis: L3 — a second text laid after the same lowering takes the
///   first's heads without reading the closure's forms.
/// - witness: `gandr-surface-lsp-diagnostics::tests::signature::a_closure_s_heads_are_read_once_per_lowering_1403`
fn closure_heads(
    key: &ClosureKey,
    read: impl FnOnce() -> Vec<Head>,
) -> Arc<[Head]>
{
    let kept = CLOSURE_HEADS
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .find(|entry| entry.0 == *key)
        .map(|entry| Arc::clone(&entry.1));
    if let Some(heads) = kept {
        return heads;
    }
    let heads: Arc<[Head]> = Arc::from(read());
    let mut kept = CLOSURE_HEADS.lock().unwrap_or_else(PoisonError::into_inner);
    kept.retain(|entry| entry.0.holding() == Holding::Held);
    kept.push((key.clone(), Arc::clone(&heads)));
    drop(kept);
    heads
}

impl Signatures
{
    /// The heads the closure a text is laid after writes, for the tests of
    /// the crates above.
    ///
    /// # Specification
    /// trivial.
    #[cfg(any(test, feature = "fixture"))]
    #[must_use]
    #[inline]
    pub const fn closure(&self) -> &Arc<[Head]>
    {
        &self.closure
    }

    /// The heads the text's own forms write, for the tests of the crates
    /// above.
    ///
    /// # Specification
    /// trivial.
    #[cfg(any(test, feature = "fixture"))]
    #[must_use]
    #[inline]
    pub fn own(&self) -> &[Head]
    {
        &self.own
    }
}

/// [`closure_heads`], for the tests of the crates above.
///
/// # Specification
/// trivial.
#[cfg(any(test, feature = "fixture"))]
#[inline]
pub fn kept_closure_heads<Read>(
    key: &ClosureKey,
    read: Read,
) -> Arc<[Head]>
where
    Read: FnOnce() -> Vec<Head>,
{
    closure_heads(key, read)
}

/// What asked for signature help: the author or a character that opens or
/// separates arguments, or a space typed after a head.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Opened
{
    /// The author, or `(` or `,`: the help answers every spine.
    Asked,
    /// A space: the help answers only while the innermost spine's declared head
    /// takes a parameter at its slot.
    Spaced,
}

/// One spine a position stands in, as the faces read it: the frame, and the
/// declared head its head refers to when the hovering keeps one.
#[derive(Clone, Copy, Debug)]
struct Spine<'hovering>
{
    /// The head, the slot and the argument written in the slot.
    frame: Frame,
    /// The declared head that the head refers to.
    declared: Option<&'hovering Signature>,
}

impl Spine<'_>
{
    /// The slot of the spine, when the declared head takes a parameter there;
    /// none past the last parameter and with no declared head.
    ///
    /// # Specification
    /// trivial.
    fn filled(&self) -> Option<ParameterSlot>
    {
        let slot = usize::from(self.frame.slot);
        self.declared
            .filter(|declared| slot < declared.parameters().len())
            .map(|_| ParameterSlot(slot))
    }
}

/// The spines that `at`, a byte of `text`, stands in, from the innermost
/// outward, `text` read as `reading` reads it and kept as `hovering` keeps it.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: the spines of [`Reading::frames`] at `at`, each with the declared
///   head the type table refers its head's first byte to, when the hovering
///   keeps one. When spaces or tabs come just before `at`, one spine more opens
///   before them, unless the frames hold its head already. That spine is the
///   innermost spine whose argument ends where those blanks start, at its next
///   slot. With no such spine, it is the use that ends there, at its first
///   slot. It opens only while its declared head takes a parameter at that
///   slot.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a space after a head, after an argument a head still
///   owes, after a saturated call, and inside a nested call, each asserted at
///   its exact signatures; every position of a closed and an open call agrees
///   with the context stack.
/// - witness: `gandr-surface-lsp::server::tests::a_space_opens_the_help_while_the_spine_owes_an_argument_4697`
/// - witness: `gandr-surface-lsp::server::tests::the_context_stack_agrees_with_the_hover_and_the_signature_help`
#[spec(ensures: |ret| ret.len() <= reading.frames(at).count().saturating_add(1))]
fn spines<'hovering>(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &'hovering Hovering,
    at: ByteOffset,
) -> Vec<Spine<'hovering>>
{
    let spine = |frame: Frame| Spine {
        declared: declared(hovering, frame.head),
        frame,
    };
    let mut found: Vec<Spine<'hovering>> = reading.frames(at).map(spine).collect();
    let start = usize::from(at);
    let before = <&str>::from(text)
        .get(.. start)
        .map_or(start, |written| written.trim_end_matches([' ', '\t']).len());
    if before == start {
        return found;
    }
    let blank = ByteOffset::from(before);
    let ended = reading.frames(blank).find(|frame| {
        frame
            .argument
            .is_some_and(|argument| argument.end() == blank)
    });
    let opened = if let Some(frame) = ended {
        Frame {
            slot: Slot::from(usize::from(frame.slot).saturating_add(1)),
            argument: None,
            ..frame
        }
    }
    else {
        let Some(last) = before.checked_sub(1)
        else {
            return found;
        };
        match hovering.table().referent(ByteOffset::from(last)) {
            Maybe::Present((head, _)) if head.end() == blank => Frame {
                head,
                slot: Slot::from(0_usize),
                argument: None,
            },
            Maybe::Present(_) | Maybe::Absent(_) => return found,
        }
    };
    let opened = spine(opened);
    if opened.filled().is_some()
        && found
            .iter()
            .all(|held| held.frame.head != opened.frame.head)
    {
        found.insert(0, opened);
    }
    found
}

/// The type the judgement gives the term at the first byte of `head`, when
/// that term lies inside `head`, on one line in `style` as the hover spells it
/// on a page wider than every line ([`TypeTable::at_line`]).
///
/// [`TypeTable::at_line`]: gandr_surface_dispatcher::TypeTable::at_line
///
/// # Specification
/// trivial.
fn head_type(
    hovering: &Hovering,
    head: ByteSpan,
    style: Style,
) -> Option<String>
{
    match hovering.table().at_line(head.start(), style) {
        Maybe::Present(ref typed) if inside(typed, head).is_some() => {
            Some(String::from(typed.ty().as_ref()))
        },
        Maybe::Present(_) | Maybe::Absent(_) => None,
    }
}

/// Some when `typed` lies inside `within`.
///
/// # Specification
/// trivial.
fn inside(
    typed: &TypedSpan,
    within: ByteSpan,
) -> Option<()>
{
    (within.start() <= typed.span().start() && typed.span().end() <= within.end()).then_some(())
}

/// The type the judgement checked the outermost term of `argument` against
/// ([`TypeTable::outermost`]), its own type when it was checked against no
/// other, on one line in `style`; none for no argument or one the table types
/// no term inside.
///
/// [`TypeTable::outermost`]: gandr_surface_dispatcher::TypeTable::outermost
///
/// # Specification
/// trivial.
fn expected(
    hovering: &Hovering,
    argument: Option<ByteSpan>,
    style: Style,
) -> Option<String>
{
    match hovering.table().outermost(argument?, style) {
        Maybe::Present(ref typed) => Some(String::from(match typed.expected() {
            Maybe::Present(checked) => checked.as_ref(),
            Maybe::Absent(_) => typed.ty().as_ref(),
        })),
        Maybe::Absent(_) => None,
    }
}

/// The bytes of `head` in `text`.
///
/// # Specification
/// trivial.
fn written(
    text: SourceText<'_>,
    head: ByteSpan,
) -> Option<SourceText<'_>>
{
    <&str>::from(text)
        .get(usize::from(head.start()) .. usize::from(head.end()))
        .map(SourceText::from)
}

/// The signature of `spine` of `text` to a client that takes a parameter as
/// its place in the label when `offsets` holds: its declared head, or the head
/// as written with the type `hovering` gives it in `style` when it has none.
///
/// # Specification
/// trivial.
fn informed(
    text: SourceText<'_>,
    hovering: &Hovering,
    spine: &Spine<'_>,
    offsets: LabelOffsets,
    style: Style,
) -> SignatureInformation
{
    let Some(signature) = spine.declared
    else {
        let head = written(text, spine.frame.head).map_or("", <&str>::from);
        return SignatureInformation {
            label: head_type(hovering, spine.frame.head, style)
                .map_or_else(|| String::from(head), |ty| format!("{head} : {ty}")),
            documentation: None,
            parameters: Vec::new(),
            active_parameter: None,
        };
    };
    signature.information(offsets, spine.filled())
}

/// What a signature-help request at `position` of `text` answers.
///
/// `reading` is the reading of the text, and its copy keeps `hovering`. The
/// client takes a parameter as its place in the label when `offsets` holds.
/// `style` spells each type, and `opened` says what asked.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: one signature for each spine the position stands in ([`spines`]),
///   from the innermost outward, the first active. A spine whose head the type
///   table refers to a declaration or constructor whose head the hovering keeps
///   answers that head, with its documentation as markdown and each parameter
///   as its start and end in the label counted in UTF-16 code units when
///   `offsets` holds or as its text otherwise, with the documentation written
///   before it as markdown when it has any. Its active parameter is the one its
///   slot fills, `null` past the last parameter. Another spine answers its head
///   as written, then ` : ` and the type the judgement gives the head when it
///   gives one, with no parameters. The help's active parameter is the first
///   signature's. Nothing when the position stands in no spine, and nothing for
///   [`Opened::Spaced`] unless the innermost spine's declared head takes a
///   parameter at its slot.
/// - provides: the answer to `textDocument/signatureHelp`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function's juxtaposed call at each argument, a
///   constructor applied to no field yet, a nested call, a position past the
///   last parameter, a call of a sibling's declaration and a position in no
///   call are each asserted at their exact answer; a space after a head that
///   owes an argument opens the help, and one after a saturated call does not.
/// - witness: `gandr-surface-lsp::server::tests::signature_help_answers_the_declared_head_of_the_call`
/// - witness: `gandr-surface-lsp::tests::session::signature_help_reads_a_sibling_s_head`
/// - witness: `gandr-surface-lsp::server::tests::signature_help_sends_a_parameter_s_documentation_1116`
/// - witness: `gandr-surface-lsp::server::tests::a_space_opens_the_help_while_the_spine_owes_an_argument_4697`
#[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Signatures(_)))]
#[must_use]
#[inline]
pub fn help(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    (offsets, style): (LabelOffsets, Style),
    opened: Opened,
) -> Answer
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let spines = spines(text, reading, hovering, at);
    let Some(innermost) = spines.first()
    else {
        return Answer::Nothing;
    };
    if opened == Opened::Spaced && innermost.filled().is_none() {
        return Answer::Nothing;
    }
    let signatures: Vec<SignatureInformation> = spines
        .iter()
        .map(|spine| informed(text, hovering, spine, offsets, style))
        .collect();
    Answer::Signatures(SignatureHelp {
        active_parameter: signatures.first().and_then(|first| first.active_parameter),
        signatures,
        active_signature: 0,
    })
}

/// The declared head of the declaration or constructor the head at `head`
/// refers to, when the hovering keeps one.
///
/// # Specification
/// trivial.
fn declared(
    hovering: &Hovering,
    head: ByteSpan,
) -> Option<&Signature>
{
    let Maybe::Present((_, referent)) = hovering.table().referent(head.start())
    else {
        return None;
    };
    hovering.signatures().declared(&referent)
}

/// What a `gandr/stack` request at `position` of `text` answers.
///
/// `reading` is the reading of the text, and its copy keeps `hovering`. The
/// answer is each spine the position stands in, from the innermost outward,
/// each type spelled in `style` on one line.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: one row for each spine the position stands in ([`spines`]), in
///   its order. A row holds the head as written and its range, and the type the
///   table gives the term at the head's first byte when that term lies inside
///   the head, as the hover spells it on a page wider than every line
///   ([`TypeTable::at_line`]). It holds the declared head and its count of
///   parameters when the table refers the head's first byte to a declaration or
///   constructor whose head the hovering keeps. It holds the slot, and the type
///   the judgement checked the outermost term of the slot's argument against
///   ([`TypeTable::outermost`]), its own type when it was checked against no
///   other. That type is none, which reads owed, when the slot writes no
///   argument or the table types no term inside it.
/// - provides: the answer to `gandr/stack`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — at every position of a closed call and of an open one,
///   each row agrees with the hover at its head, and the rows with the
///   signatures of the signature help.
/// - witness: `gandr-surface-lsp::server::tests::the_context_stack_agrees_with_the_hover_and_the_signature_help`
///
/// [`TypeTable::at_line`]: gandr_surface_dispatcher::TypeTable::at_line
/// [`TypeTable::outermost`]: gandr_surface_dispatcher::TypeTable::outermost
#[spec(ensures: |ret| matches!(ret, Answer::Stack(_)))]
#[must_use]
#[inline]
pub fn stack(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    style: Style,
) -> Answer
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    Answer::Stack(
        spines(text, reading, hovering, at)
            .into_iter()
            .filter_map(|spine| {
                Some(StackRow {
                    range: ranged(&index, spine.frame.head)?,
                    head: String::from(<&str>::from(written(text, spine.frame.head)?)),
                    ty: head_type(hovering, spine.frame.head, style),
                    declared: spine
                        .declared
                        .map(|declared| String::from(<&str>::from(declared.label()))),
                    arity: spine
                        .declared
                        .and_then(|declared| u32::try_from(declared.parameters().len()).ok()),
                    slot: u32::try_from(usize::from(spine.frame.slot)).unwrap_or(u32::MAX),
                    expected: expected(hovering, spine.frame.argument, style),
                })
            })
            .collect(),
    )
}

/// The stack card at `position` of `text`, whose reading is `reading` and
/// whose copy keeps `hovering`, each type spelled in `style` on one line.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: the card at the position's byte offset, one row for each spine
///   the position stands in ([`spines`]), in its order. A row holds the head as
///   written, the slot, and the expected type as [`stack`] answers them. A
///   spine with a declared head holds its arity, and as its type the declared
///   head past its name and the `:` after it, with the run that the parameter
///   at its slot writes there. Another spine holds the type the judgement gives
///   its head, with no run.
/// - provides: the card the render bus sends for the cursor of a document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an attached view hears the card of the cursor the
///   editor's signature help names, its innermost row's run the parameter its
///   slot fills, and a card again once an edit changes the stack there.
/// - witness: `gandr-surface-lsp::hub::tests::an_attached_view_follows_the_stack_at_the_editors_cursor`
#[spec(ensures: |ret| ret.rows.iter().all(|row| row.filled.is_none() || row.ty.is_some()))]
#[must_use]
#[inline]
pub fn card(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    style: Style,
) -> StackCard
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let count = |value: usize| Count(u64::try_from(value).unwrap_or(u64::MAX));
    let rows = spines(text, reading, hovering, at)
        .into_iter()
        .filter_map(|spine| {
            let head = String::from(<&str>::from(written(text, spine.frame.head)?));
            let (ty, filled) = spine.declared.map_or_else(
                || (head_type(hovering, spine.frame.head, style), None),
                |signature| {
                    (
                        signature.ty().map(|ty| String::from(<&str>::from(ty))),
                        signature.run(ParameterSlot(usize::from(spine.frame.slot))),
                    )
                },
            );
            Some(SpineRow {
                head,
                ty,
                filled,
                slot: count(usize::from(spine.frame.slot)),
                arity: spine
                    .declared
                    .map(|declared| count(declared.parameters().len())),
                expected: expected(hovering, spine.frame.argument, style),
            })
        })
        .collect();
    StackCard {
        offset: gandr_surface_render_remote::ByteOffset::from(usize::from(at)),
        rows,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_lowering::Unit;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;

    use super::Signatures;
    use crate::toolkit::grammar;
    use crate::toolkit::roles;

    #[test]
    fn each_head_reads_its_parameters()
    {
        // `plus`'s head stays over two lines, so a label reads its layout
        // collapsed.
        let text = include_str!("signature/unformatted/heads.gandr");
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let read: Vec<(String, String, Vec<String>, Option<String>)> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let name = text
                    .get(usize::from(named.start()) .. usize::from(named.end()))
                    .unwrap_or_default();
                let parameters = signature
                    .parameters()
                    .map(|(written, _)| String::from(<&str>::from(written)))
                    .collect();
                (
                    String::from(name),
                    String::from(<&str>::from(signature.label())),
                    parameters,
                    signature
                        .documentation()
                        .map(|documented| String::from(<&str>::from(documented))),
                )
            })
            .collect();
        let head = |name: &str, label: &str, parameters: &[&str], documentation: Option<&str>| {
            (
                String::from(name),
                String::from(label),
                parameters
                    .iter()
                    .map(|&parameter| String::from(parameter))
                    .collect::<Vec<_>>(),
                documentation.map(String::from),
            )
        };
        assert_eq!(read, [
            head("Nat", "Nat : Type", &[], Some("Natural numbers.")),
            head("Zero", "Zero : Nat", &[], None),
            head(
                "Succ",
                "Succ : (n : Nat) --> Nat",
                &["n : Nat"],
                Some("One more.")
            ),
            head(
                "plus",
                "plus(n : Nat, m : Nat) -> -F Nat",
                &["n : Nat", "m : Nat"],
                Some("Addition.")
            ),
            head(
                "double",
                "double : +U (Nat -> Nat -> -F Nat)",
                &["Nat", "Nat"],
                None
            ),
            head("List", "List(a : Type) : Type", &["a : Type"], None),
            head("Nil", "Nil : List(a)", &[], None),
            head(
                "Cons",
                "Cons : (head : a, tail : List(a)) --> List(a)",
                &["head : a", "tail : List(a)"],
                None
            ),
            head(
                "ap",
                "ap(f : +U (Nat -> -F Nat), x : Nat) -> -F Nat",
                &["f : +U (Nat -> -F Nat)", "x : Nat"],
                None
            ),
            head("f", "f : +U (Nat -> -F Nat)", &["Nat"], None),
            head(
                "r",
                "r : *{ sub : +U (Nat -> Nat -> -F Type), subTm : (g : Nat, t : sub(g, g)) -> Nat }",
                &[],
                None
            ),
            head(
                "sub",
                "sub : +U (Nat -> Nat -> -F Type)",
                &["Nat", "Nat"],
                None
            ),
            head(
                "subTm",
                "subTm : (g : Nat, t : sub(g, g)) -> Nat",
                &["g : Nat", "t : sub(g, g)"],
                None
            ),
        ]);
    }

    /// #1116: a `///` run written before a parameter documents it, in a
    /// declaration's parameter list and in a constructor's telescope, and a
    /// list laid over lines labels as one line.
    #[test]
    fn a_parameter_reads_the_documentation_written_before_it_1116()
    {
        // A head as read: its name, its label, each parameter's text with
        // its documentation, and the head's documentation.
        type Read = (
            String,
            String,
            Vec<(String, Option<String>)>,
            Option<String>,
        );
        let text = include_str!("signature/fixtures/documented-parameters.gandr");
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let read: Vec<Read> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let name = text
                    .get(usize::from(named.start()) .. usize::from(named.end()))
                    .unwrap_or_default();
                let parameters = signature
                    .parameters()
                    .map(|(written, documented)| {
                        (
                            String::from(<&str>::from(written)),
                            documented.map(|documented| String::from(<&str>::from(documented))),
                        )
                    })
                    .collect();
                (
                    String::from(name),
                    String::from(<&str>::from(signature.label())),
                    parameters,
                    signature
                        .documentation()
                        .map(|documented| String::from(<&str>::from(documented))),
                )
            })
            .collect();
        let documented = |parameter: &str, documentation: Option<&str>| {
            (String::from(parameter), documentation.map(String::from))
        };
        assert_eq!(read, [
            (
                String::from("Nat"),
                String::from("Nat : Type"),
                Vec::new(),
                None
            ),
            (
                String::from("Zero"),
                String::from("Zero : Nat"),
                Vec::new(),
                None
            ),
            (
                String::from("Succ"),
                String::from("Succ : (n : Nat) --> Nat"),
                Vec::from([documented("n : Nat", Some("The predecessor."))]),
                Some(String::from("One more.")),
            ),
            (
                String::from("plus"),
                String::from("plus(n : Nat, m : Nat, k : Nat) -> -F Nat"),
                Vec::from([
                    documented("n : Nat", Some("The first summand.")),
                    documented("m : Nat", Some("The second\nsummand.")),
                    documented("k : Nat", None),
                ]),
                Some(String::from("Addition.")),
            ),
        ]);
    }

    /// A run documents the one parameter or member written after it: not the
    /// member after a documented telescope, not a function type's domain it
    /// sits inside, which the label leaves out; a parameter whose type holds a
    /// comma is one parameter; the documented parameters are keyed by their
    /// name tiles.
    #[test]
    fn a_run_documents_only_what_it_is_written_before_1800()
    {
        let text = include_str!("signature/fixtures/documented-runs.gandr");
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let spelled = |span: super::ByteSpan| {
            text.get(usize::from(span.start()) .. usize::from(span.end()))
                .unwrap_or_default()
        };
        let read: Vec<_> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let parameters: Vec<_> = signature
                    .parameters()
                    .map(|(written, documented)| {
                        (<&str>::from(written), documented.map(<&str>::from))
                    })
                    .collect();
                (
                    spelled(named),
                    <&str>::from(signature.label()),
                    parameters,
                    signature.documentation().map(<&str>::from),
                )
            })
            .collect();
        assert_eq!(read, [
            ("Nat", "Nat : Type", Vec::new(), None),
            ("Zero", "Zero : Nat", Vec::new(), None),
            (
                "Succ",
                "Succ : (n : Nat) --> Nat",
                Vec::from([("n : Nat", Some("The predecessor."))]),
                None
            ),
            ("Two", "Two : Nat", Vec::new(), None),
            ("Three", "Three : Nat", Vec::new(), Some("Three.")),
            (
                "apply",
                "apply(f : (x : Nat) -> -F Nat, p : (a : Nat, b : Nat), y : Nat) -> -F Nat",
                Vec::from([
                    ("f : (x : Nat) -> -F Nat", None),
                    ("p : (a : Nat, b : Nat)", Some("The pair.")),
                    ("y : Nat", None),
                ]),
                None
            ),
            (
                "f",
                "f : (x : Nat) -> -F Nat",
                Vec::from([("x : Nat", Some("The argument."))]),
                None
            ),
            (
                "use",
                "use(h : (i : Nat) -> Nat) -> -F Nat",
                Vec::from([("h : (i : Nat) -> Nat", None)]),
                None
            ),
            (
                "h",
                "h : (i : Nat) -> Nat",
                Vec::from([("i : Nat", Some("The index."))]),
                None
            ),
        ]);
        let documented: Vec<_> = heads
            .documented
            .iter()
            .map(|&((_, named), ref documentation)| (spelled(named), documentation.as_str()))
            .collect();
        assert_eq!(documented, [
            ("n", "The predecessor."),
            ("x", "The argument."),
            ("p", "The pair."),
            ("i", "The index.")
        ]);
    }

    /// #1810: a list's own parentheses nested inside a parameter, as a
    /// binder writes them, keep the parameter whole, and a type returning a
    /// function is no function type, so its head takes no parameter.
    #[test]
    fn only_a_function_type_and_a_list_s_own_separators_make_parameters_1810()
    {
        let text = include_str!(
            "signature/unformatted/only-a-function-type-and-a-list-s-own-separators-make-parameters-1810.gandr"
        );
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let read: Vec<_> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let parameters: Vec<_> = signature
                    .parameters()
                    .map(|(written, _)| <&str>::from(written))
                    .collect();
                (
                    text.get(usize::from(named.start()) .. usize::from(named.end()))
                        .unwrap_or_default(),
                    <&str>::from(signature.label()),
                    parameters,
                )
            })
            .collect();
        assert_eq!(read, [
            ("Lambda", "Lambda", Vec::new()),
            ("Tm", "Tm : Type", Vec::new()),
            (
                "lam",
                "lam : (t : pi+ (x : Tm) . Tm) --> Tm",
                Vec::from(["t : pi+ (x : Tm) . Tm"])
            ),
            (
                "app",
                "app : (t : Tm, u : Tm) --> Tm",
                Vec::from(["t : Tm", "u : Tm"])
            ),
            ("g", "g : -F (Nat -> -F Nat)", Vec::new()),
        ]);
    }
}
