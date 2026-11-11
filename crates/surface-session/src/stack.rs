//! The context stack: every spine that encloses an offset, innermost first.
//!
//! # The form store keeps the spines of each form beside its region
//!
//! **Choice.** A spine is one application the parser molded: a juxtaposed
//! application `f x y`, with its head, where its first slot opens, where each
//! slot but the last ends and where it closes; or a family's application
//! `List(a)` that writes its own `(`, with its `,` tiles and its `)`. The form
//! store reads the spines of each form it joins off the molded tree, which
//! holds the parser's repairs, and keeps them with the region it lays for the
//! form. Their offsets count from the start of the form's region, so a form
//! that the next parse takes up whole keeps its spines as they are, and a
//! keystroke reads the spines of the forms it joins and no others. A query
//! takes the form whose region holds the offset and walks its spines from the
//! innermost outward. It reads no type: a face takes the head's type and the
//! type a slot was checked against from the judgement's type table.
//!
//! **Alternatives.** The language server read every call of a text off the
//! whole tree once per change and answered the innermost call only. That walk
//! costs the whole text on each change, and a second index of the same spines
//! could disagree with this one.
//!
//! **Reversal.** A face that asks about a text the session did not parse reads
//! the spines off its own tree ([`Stack::of`]). A form whose spines the
//! molding itself records would remove the walk after the join.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteLength;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;

/// The rule of a family's application, `List(a)`.
const APPLICATION: &str = "type_application";

/// A run of entries in one of a form's buffers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Entries
{
    /// The first entry.
    start: u32,
    /// One past the last entry.
    end: u32,
}

impl Entries
{
    /// The entries from `start` to the end of a buffer of `length` entries.
    ///
    /// # Specification
    /// trivial.
    fn since(
        start: usize,
        length: usize,
    ) -> Self
    {
        Self {
            start: u32::try_from(start).unwrap_or(u32::MAX),
            end: u32::try_from(length).unwrap_or(u32::MAX),
        }
    }

    /// The entries of `buffer` this run names.
    ///
    /// # Specification
    /// trivial.
    fn of<T>(
        self,
        buffer: &[T],
    ) -> &[T]
    {
        let at = |index: u32| usize::try_from(index).unwrap_or(usize::MAX);
        buffer
            .get(at(self.start) .. at(self.end))
            .unwrap_or_default()
    }
}

/// One spine of a form, each offset counted from the start of the form's
/// region.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Spine
{
    /// The bytes of the head.
    head: ByteSpan,
    /// Just past the `(` that opens the slots, or the start of the first
    /// argument of a juxtaposed application.
    open: ByteOffset,
    /// The start of the written `)`, or the end of the application when the
    /// parser closed it or it is juxtaposed.
    close: ByteOffset,
    /// The start of each `,` between the slots, or the end of each argument
    /// but the last, ascending.
    separators: Entries,
    /// The bytes of each argument written, ascending.
    arguments: Entries,
    /// The position of the innermost spine that holds this one, among the
    /// form's spines in order.
    holder: Option<u32>,
}

/// The spines of one form, ascending by where their slots open.
///
/// # Specification
/// - requires: built by [`Stack::of`] or the form store's parse.
/// - ensures: ascending by opening; every holder is the position of a spine
///   that holds the spine naming it; each spine's separators and arguments are
///   ascending.
/// - panics: none.
/// - executable: none — a carrier; the read and [`Stack::at`] carry the
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Stack::at`].
/// - witness: `stack::tests::the_innermost_spine_answers_with_its_slot`
#[derive(Debug, Eq, PartialEq)]
pub struct Spines
{
    /// The spines.
    each: Box<[Spine]>,
    /// The separators of every spine, by spine.
    separators: Box<[ByteOffset]>,
    /// The arguments of every spine, by spine.
    arguments: Box<[ByteSpan]>,
}

impl Spines
{
    /// The spines of `forms`, top-level children of `tree` parsed under
    /// `grammar`, each offset counted from `origin`; none when they hold no
    /// spine.
    ///
    /// # Specification
    /// - requires: `tree` was parsed under `grammar`; `forms` are children of
    ///   its root that start at or after `origin`.
    /// - ensures: one spine per juxtaposed application whose left operands down
    ///   to its head are applications: its innermost left operand as its head,
    ///   the start of its first argument as its opening, the end of each
    ///   argument but the last as a separator, each argument, and its end as
    ///   its close. One spine per family application that writes an opening `(`
    ///   among its own tiles: its first child as its head, its own `,` tiles as
    ///   separators, the children between its brackets as its arguments, and
    ///   its own `)` as its close, or its end when the parser closed it.
    ///   Ascending by opening, each naming the innermost spine that holds it;
    ///   the inner applications of a juxtaposed spine are no spines of their
    ///   own.
    /// - provides: the spines the form store keeps with a form's region.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the forms with an explicit stack, and one sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested spine, a spine in an argument's brackets, a
    ///   recursive call and a family's application are each found where they
    ///   are written.
    /// - witness: `stack::tests::the_innermost_spine_answers_with_its_slot`
    /// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|spines| !spines.each.is_empty()
        && spines.each.windows(2).all(|pair| matches!(pair, [first, second] if first.open <= second.open))))]
    pub(crate) fn read(
        grammar: &Pbg,
        tree: &SyntaxTree<'_>,
        forms: &[NodeIndex],
        origin: ByteOffset,
    ) -> Option<Self>
    {
        let mut walk = Walk {
            grammar,
            tree,
            origin: usize::from(origin),
            separators: Vec::new(),
            arguments: Vec::new(),
            parts: Vec::new(),
        };
        let mut found: Vec<Spine> = Vec::new();
        let mut pending: Vec<(NodeIndex, Option<u32>)> =
            forms.iter().map(|&form| (form, None)).collect();
        while let Some((at, holder)) = pending.pop() {
            if let Some(mut spine) = walk.juxtaposed(at) {
                spine.holder = holder;
                found.push(spine);
                let holder = u32::try_from(found.len().saturating_sub(1)).ok();
                pending.extend(walk.parts.iter().map(|&part| (part, holder)));
                continue;
            }
            let below = walk.applied(at).map_or(holder, |mut spine| {
                spine.holder = holder;
                found.push(spine);
                u32::try_from(found.len().saturating_sub(1)).ok()
            });
            pending.extend(tree.children(at).map(|child| (child, below)));
        }
        if found.is_empty() {
            return None;
        }
        let mut order: Vec<u32> = (0 .. found.len())
            .filter_map(|position| u32::try_from(position).ok())
            .collect();
        order.sort_by_key(|&position| spine_at(&found, position).map(|spine| spine.open));
        let mut placed = alloc::vec![0_u32; found.len()];
        for (rank, &position) in order.iter().enumerate() {
            if let Some(slot) = placed.get_mut(usize::try_from(position).unwrap_or(usize::MAX)) {
                *slot = u32::try_from(rank).unwrap_or(u32::MAX);
            }
        }
        let place = |holder: u32| {
            placed
                .get(usize::try_from(holder).unwrap_or(usize::MAX))
                .copied()
        };
        let spines: Box<[Spine]> = order
            .iter()
            .filter_map(|&position| spine_at(&found, position).copied())
            .map(|spine| Spine {
                holder: spine.holder.and_then(place),
                ..spine
            })
            .collect();
        Some(Self {
            each: spines,
            separators: walk.separators.into_boxed_slice(),
            arguments: walk.arguments.into_boxed_slice(),
        })
    }

    /// The spines that hold `offset`, counted from the form's start, from the
    /// innermost outward.
    ///
    /// # Specification
    /// trivial.
    fn holding(
        &self,
        offset: ByteOffset,
    ) -> impl Iterator<Item = &Spine> + '_
    {
        let last = self.each.partition_point(|spine| spine.open <= offset);
        let mut at = last
            .checked_sub(1)
            .and_then(|position| u32::try_from(position).ok());
        core::iter::from_fn(move || {
            while let Some(spine) = at.and_then(|position| spine_at(&self.each, position)) {
                at = spine.holder;
                if spine.open <= offset && offset <= spine.close {
                    return Some(spine);
                }
            }
            None
        })
    }
}

/// The spine at `position` of `spines`.
///
/// # Specification
/// trivial.
fn spine_at(
    spines: &[Spine],
    position: u32,
) -> Option<&Spine>
{
    spines.get(usize::try_from(position).unwrap_or(usize::MAX))
}

/// One walk of a form's tree: what it reads under, and the buffers it fills.
struct Walk<'walk, 'source>
{
    /// The grammar the tree was parsed under.
    grammar: &'walk Pbg,
    /// The tree.
    tree: &'walk SyntaxTree<'source>,
    /// The offset every spine counts from.
    origin: usize,
    /// The separators of the spines found so far.
    separators: Vec<ByteOffset>,
    /// The arguments of the spines found so far.
    arguments: Vec<ByteSpan>,
    /// The head and the arguments of the latest juxtaposed spine.
    parts: Vec<NodeIndex>,
}

impl Walk<'_, '_>
{
    /// `at`, counted from the walk's origin.
    ///
    /// # Specification
    /// trivial.
    fn offset(
        &self,
        at: ByteOffset,
    ) -> ByteOffset
    {
        ByteOffset::from(usize::from(at).saturating_sub(self.origin))
    }

    /// `span`, counted from the walk's origin.
    ///
    /// # Specification
    /// trivial.
    fn span(
        &self,
        span: ByteSpan,
    ) -> ByteSpan
    {
        ByteSpan::new(self.offset(span.start()), self.offset(span.end())).unwrap_or(span)
    }

    /// The spine the family application at `at` is, when it writes its
    /// opening `(`; its separators and arguments are pushed onto the walk's
    /// buffers.
    ///
    /// # Specification
    /// trivial.
    fn applied(
        &mut self,
        at: NodeIndex,
    ) -> Option<Spine>
    {
        let (grammar, tree) = (self.grammar, self.tree);
        let node = tree.node(at)?;
        let NodeLabel::Meld(mold) = node.label()
        else {
            return None;
        };
        let rule = grammar.rule_of(mold).ok()?.name().0;
        if rule != APPLICATION {
            return None;
        }
        let (separated, argued) = (self.separators.len(), self.arguments.len());
        let mut head = None;
        let mut open = None;
        let mut close = node.span().end();
        for child in tree.children(at) {
            let Some(held) = tree.node(child)
            else {
                continue;
            };
            match held.label() {
                NodeLabel::Tile(tile)
                    if grammar
                        .rule_of(tile)
                        .is_ok_and(|owner| owner.name().0 == rule) =>
                {
                    match tree.fragment(child).map(<&str>::from) {
                        Some("(") if open.is_none() => open = Some(held.span().end()),
                        Some(",") if open.is_some() => {
                            let separator = self.offset(held.span().start());
                            self.separators.push(separator);
                        },
                        Some(")") if open.is_some() => close = held.span().start(),
                        Some(_) | None => {},
                    }
                    if head.is_none() {
                        head = Some(held.span());
                    }
                },
                NodeLabel::Meld(_) | NodeLabel::Tile(_) => {
                    if head.is_none() {
                        head = Some(held.span());
                    }
                    else if open.is_some() {
                        let argument = self.span(held.span());
                        self.arguments.push(argument);
                    }
                },
                NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space
                | NodeLabel::Doc => {},
            }
        }
        let (Some(head), Some(open)) = (head, open)
        else {
            self.separators.truncate(separated);
            self.arguments.truncate(argued);
            return None;
        };
        Some(Spine {
            head: self.span(head),
            open: self.offset(open),
            close: self.offset(close),
            separators: Entries::since(separated, self.separators.len()),
            arguments: Entries::since(argued, self.arguments.len()),
            holder: None,
        })
    }

    /// The spine the juxtaposed application at `at` writes, `f x y`, with its
    /// head and then its arguments left in the walk's parts; its separators
    /// and arguments are pushed onto the walk's buffers. It walks down the
    /// spine's left edge once.
    ///
    /// # Specification
    /// - requires: the walk's tree was parsed under its grammar.
    /// - ensures: when `at` is an application whose left operands down to its
    ///   head are applications, each with its three parts written, the spine
    ///   with the innermost left operand as its head, the start of the first
    ///   argument as its opening, the end of each argument but the last as a
    ///   separator, each argument, and the end of `at` as its close; none
    ///   otherwise.
    /// - panics: none.
    /// - executable: none — a clause would walk the spine again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spines::read`].
    /// - witness: `stack::tests::the_innermost_spine_answers_with_its_slot`
    fn juxtaposed(
        &mut self,
        at: NodeIndex,
    ) -> Option<Spine>
    {
        let tree = self.tree;
        let application = self.grammar.application()?;
        let applied = |position: NodeIndex| {
            tree.node(position)
                .is_some_and(|node| node.label() == NodeLabel::Meld(application))
        };
        if !applied(at) {
            return None;
        }
        let close = tree.node(at)?.span().end();
        // The arguments are met last to first, then reversed.
        self.parts.clear();
        let mut position = at;
        let head = loop {
            let mut written = tree.children(position).filter(|&child| {
                tree.node(child)
                    .is_some_and(|node| !matches!(node.label(), NodeLabel::Space | NodeLabel::Doc))
            });
            let (Some(left), Some(_), Some(right), None) = (
                written.next(),
                written.next(),
                written.next(),
                written.next(),
            )
            else {
                return None;
            };
            self.parts.push(right);
            if applied(left) {
                position = left;
            }
            else {
                break left;
            }
        };
        self.parts.push(head);
        self.parts.reverse();
        let mut spans = self
            .parts
            .iter()
            .filter_map(|&part| tree.node(part).map(Node::span));
        let head = spans.next()?;
        let (separated, argued) = (self.separators.len(), self.arguments.len());
        let mut open = None;
        let mut last = None;
        for argument in spans {
            if let Some(before) = last.replace(argument) {
                let end = self.offset(before.end());
                self.separators.push(end);
            }
            else {
                open = Some(argument.start());
            }
            let counted = self.span(argument);
            self.arguments.push(counted);
        }
        let Some(open) = open
        else {
            self.separators.truncate(separated);
            self.arguments.truncate(argued);
            return None;
        };
        Some(Spine {
            head: self.span(head),
            open: self.offset(open),
            close: self.offset(close),
            separators: Entries::since(separated, self.separators.len()),
            arguments: Entries::since(argued, self.arguments.len()),
            holder: None,
        })
    }
}

/// The position of a slot among a spine's slots, from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Slot(usize);

impl From<Slot> for usize
{
    /// The position, from zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(slot: Slot) -> Self
    {
        slot.0
    }
}

/// One spine that encloses an offset: its head, the slot the offset writes,
/// and the argument written in that slot, each span in the text's own
/// coordinates.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Frame
{
    /// The bytes of the head.
    pub head: ByteSpan,
    /// The slot the offset writes: how many separators of the spine start
    /// before it.
    pub slot: Slot,
    /// The argument written in that slot, when the text writes one.
    pub argument: Option<ByteSpan>,
}

/// The spines of a text, by the form whose region holds them.
///
/// # Specification
/// - requires: built by [`Stack::of`] or the form store's parse.
/// - ensures: the forms ascend by start, and only a form that holds a spine has
///   an entry.
/// - panics: none.
/// - executable: none — a carrier; [`Stack::of`] and [`Stack::at`] carry the
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Stack::at`], and the stack the form store keeps over
///   every generated edit and every corpus edit script is the stack read off
///   the whole parse of the same text.
/// - witness: `stack::tests::the_innermost_spine_answers_with_its_slot`
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
#[derive(Clone, Debug, Default, Eq)]
pub struct Stack
{
    /// Where each form's region starts, with its spines.
    forms: Vec<(ByteOffset, Arc<Spines>)>,
}

impl Stack
{
    /// The stack of `tree`, parsed under `grammar`, one form per child of its
    /// root. It walks the tree once.
    ///
    /// # Specification
    /// - requires: `tree` was parsed under `grammar`.
    /// - ensures: per child of the root that holds a spine, its start and its
    ///   spines as [`Spines::read`] reads them from that start.
    /// - provides: the stack of a text a face parsed itself.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Stack::at`].
    /// - witness: `stack::tests::the_innermost_spine_answers_with_its_slot`
    #[inline]
    #[spec(ensures: |ret| ret.forms.windows(2).all(|pair| matches!(pair, [first, second] if first.0 <= second.0)))]
    #[must_use]
    pub fn of(
        grammar: &Pbg,
        tree: &SyntaxTree<'_>,
    ) -> Self
    {
        let forms = tree
            .children(tree.root())
            .filter_map(|form| {
                let start = tree.node(form)?.span().start();
                Spines::read(grammar, tree, &[form], start).map(|read| (start, Arc::new(read)))
            })
            .collect();
        Self { forms }
    }

    /// The stack whose forms are `forms`: where each form's region starts,
    /// with its spines.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_forms(forms: Vec<(ByteOffset, Arc<Spines>)>) -> Self
    {
        Self { forms }
    }

    /// Every spine that encloses `offset`, from the innermost outward.
    ///
    /// # Specification
    /// - requires: nothing; any offset is admitted.
    /// - ensures: the spines of the last form that starts at or before `offset`
    ///   whose slots open at or before it and close at or after it, innermost
    ///   first, each with how many of its separators start before `offset` and
    ///   the argument written between the separators around that slot; nothing
    ///   when no spine holds it.
    /// - provides: the context stack at a caret, for signature help and the
    ///   side view's pane.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a binary search for the form and one for the last spine
    ///   opened at or before `offset`, then one step per spine that holds it;
    ///   nothing is allocated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position in a nested spine answers it and each
    ///   spine around it, one past a spine's close answers the spine around it,
    ///   one in a spine's head answers the spine that holds that spine, and the
    ///   separators before the position count the slot.
    /// - witness: `stack::tests::the_innermost_spine_answers_with_its_slot`
    /// - witness: `stack::tests::every_enclosing_spine_answers_outward`
    #[inline]
    pub fn at(
        &self,
        offset: ByteOffset,
    ) -> impl Iterator<Item = Frame> + '_
    {
        let form = self
            .forms
            .partition_point(|&(start, _)| start <= offset)
            .checked_sub(1)
            .and_then(|position| self.forms.get(position));
        form.into_iter().flat_map(move |&(start, ref spines)| {
            let by = ByteLength::from(usize::from(start));
            let local = ByteOffset::from(usize::from(offset).saturating_sub(usize::from(start)));
            spines.holding(local).map(move |spine| {
                let separators = spine.separators.of(&spines.separators);
                let slot = separators.partition_point(|&separator| separator < local);
                let after = slot
                    .checked_sub(1)
                    .and_then(|before| separators.get(before))
                    .copied()
                    .unwrap_or(spine.open);
                let before = separators.get(slot).copied().unwrap_or(spine.close);
                let argument = spine
                    .arguments
                    .of(&spines.arguments)
                    .iter()
                    .find(|argument| after <= argument.start() && argument.end() <= before)
                    .map(|argument| argument.shifted(by));
                Frame {
                    head: spine.head.shifted(by),
                    slot: Slot(slot),
                    argument,
                }
            })
        })
    }

    /// Every spine of the stack in the text's own coordinates, in order, each
    /// with its holder's position among them all.
    ///
    /// # Specification
    /// trivial.
    fn flattened(
        &self
    ) -> impl Iterator<Item = (ByteSpan, ByteOffset, ByteOffset, Option<usize>)> + '_
    {
        self.forms
            .iter()
            .scan(0_usize, |base, &(start, ref spines)| {
                let first = *base;
                *base = base.saturating_add(spines.each.len());
                Some((first, start, spines))
            })
            .flat_map(|(first, start, spines)| {
                let by = ByteLength::from(usize::from(start));
                let shift = move |at: ByteOffset| {
                    ByteOffset::from(usize::from(at).saturating_add(usize::from(start)))
                };
                spines.each.iter().map(move |spine| {
                    (
                        spine.head.shifted(by),
                        shift(spine.open),
                        shift(spine.close),
                        spine.holder.map(|holder| {
                            first.saturating_add(usize::try_from(holder).unwrap_or(usize::MAX))
                        }),
                    )
                })
            })
    }

    /// Every separator of the stack in the text's own coordinates, in order.
    ///
    /// # Specification
    /// trivial.
    fn separators(&self) -> impl Iterator<Item = ByteOffset> + '_
    {
        self.forms.iter().flat_map(|&(start, ref spines)| {
            spines.each.iter().flat_map(move |spine| {
                spine
                    .separators
                    .of(&spines.separators)
                    .iter()
                    .map(move |&at| {
                        ByteOffset::from(usize::from(at).saturating_add(usize::from(start)))
                    })
            })
        })
    }

    /// Every argument of the stack in the text's own coordinates, in order.
    ///
    /// # Specification
    /// trivial.
    fn arguments(&self) -> impl Iterator<Item = ByteSpan> + '_
    {
        self.forms.iter().flat_map(|&(start, ref spines)| {
            let by = ByteLength::from(usize::from(start));
            spines.each.iter().flat_map(move |spine| {
                spine
                    .arguments
                    .of(&spines.arguments)
                    .iter()
                    .map(move |argument| argument.shifted(by))
            })
        })
    }
}

impl PartialEq for Stack
{
    /// Whether both stacks hold the same spines in the text's own
    /// coordinates, whatever forms they are kept by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.flattened().eq(other.flattened())
            && self.separators().eq(other.separators())
            && self.arguments().eq(other.arguments())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_grammar::built_in;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;

    use super::Stack;

    /// A family, a function that matches on it, a call that nests a
    /// constructor, and a family applied in a type.
    const CALLED: &str = include_str!("stack/fixtures/called.gandr");

    /// The frames at the first byte of `marker` in `text`: each head as
    /// written, its slot, and the argument written there.
    ///
    /// # Specification
    /// trivial.
    fn frames(
        text: &str,
        marker: &str,
    ) -> Vec<(String, usize, Option<String>)>
    {
        let grammar = built_in().expect("the grammar builds");
        let parsed = parse(&grammar, SourceText::from(text)).expect("the text parses");
        let at = text.find(marker).expect("the marker occurs");
        let written = |span: ByteSpan| {
            String::from(
                text.get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or_default(),
            )
        };
        Stack::of(&grammar, parsed.tree())
            .at(ByteOffset::from(at))
            .map(|frame| {
                (
                    written(frame.head),
                    usize::from(frame.slot),
                    frame.argument.map(written),
                )
            })
            .collect()
    }

    /// The innermost frame at `marker` in `text`: its head and slot.
    ///
    /// # Specification
    /// trivial.
    fn innermost(
        text: &str,
        marker: &str,
    ) -> Option<(String, usize)>
    {
        frames(text, marker)
            .into_iter()
            .next()
            .map(|(head, slot, _)| (head, slot))
    }

    #[test]
    fn the_innermost_spine_answers_with_its_slot()
    {
        let answer = |head: &str, slot: usize| Some((String::from(head), slot));
        assert_eq!(
            innermost(CALLED, "Zero) Zero"),
            answer("Succ", 0),
            "a spine nested in an argument answers itself"
        );
        assert_eq!(
            innermost(CALLED, " Zero }"),
            answer("plus", 0),
            "just past an argument, the argument it ends"
        );
        assert_eq!(
            innermost(CALLED, "Zero }"),
            answer("plus", 1),
            "at the next argument, that argument"
        );
        assert_eq!(
            innermost(
                CALLED,
                include_str!("stack/unformatted/the-innermost-spine-answers-with-its-slot-1.gandr")
            ),
            answer("plus", 1),
            "just past the last argument, the spine it ends"
        );
        assert_eq!(
            innermost(
                CALLED,
                include_str!("stack/unformatted/the-innermost-spine-answers-with-its-slot-2.gandr")
            ),
            None,
            "past the spine, no spine"
        );
        assert_eq!(
            innermost(CALLED, "plus (Succ"),
            None,
            "on the head, not the spine it heads"
        );
        assert_eq!(
            innermost(
                CALLED,
                include_str!("stack/unformatted/the-innermost-spine-answers-with-its-slot-3.gandr")
            ),
            answer("plus[<]", 1),
            "a recursive call, headed by its claim"
        );
        assert_eq!(
            innermost(CALLED, "a)\n"),
            answer("List", 0),
            "a family's application in a type"
        );
    }

    #[test]
    fn every_enclosing_spine_answers_outward()
    {
        // `main` nests three spines; the open call below it closes none.
        let closed = "def main() -> -F Integer { f 1 (g 2 (h ?)) }\n";
        let frame = |head: &str, slot: usize, argument: Option<&str>| {
            (String::from(head), slot, argument.map(String::from))
        };
        assert_eq!(
            frames(closed, "?"),
            [
                frame("h", 0, Some("?")),
                frame("g", 1, Some("(h ?)")),
                frame("f", 1, Some("(g 2 (h ?))")),
            ],
            "the hole stands in each spine around it, innermost first"
        );
        assert_eq!(
            frames(closed, "h ?"),
            [
                frame("g", 1, Some("(h ?)")),
                frame("f", 1, Some("(g 2 (h ?))"))
            ],
            "a head stands in the spines around its own"
        );
        assert_eq!(
            frames(closed, "f 1"),
            [],
            "the outermost head stands in no spine"
        );
        let open = "def main() -> -F Integer { f 1 (g 2 (h \n";
        let at = |marker: &str| {
            frames(open, marker)
                .into_iter()
                .map(|(head, slot, _)| (head, slot))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            at("2 (h"),
            [(String::from("g"), 0), (String::from("f"), 1)],
            "an open call keeps the spines the parser repaired"
        );
    }
}
