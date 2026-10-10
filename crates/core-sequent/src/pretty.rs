//! The IL's concrete notation: a command, producer or consumer rendered as
//! text, for inspection, debugging and diagnostics.
//!
//! ```text
//! ⟨p |+ c⟩  ⟨p |− c⟩            cuts
//! x0  l0  c3  42  "text"         variables (intuitionistic, linear), constants, literals
//! ()  pair(p, q)  inl(p)  inr(p)  lift(p)
//! {force(α) ⇒ s}  cocase {apply(x; α) ⇒ s}  μα. s
//! α0  μ̃x. s  apply(p; c)  force(c)  case {inl(x) ⇒ s | inr(x) ⇒ s}  ★
//! ```
//!
//! Binders are written without names: an occurrence's index says which binder
//! it reads, counting outward. Rendering is bounded: past a nesting depth of
//! 64 a node renders as `…`, so the output's size is bounded whatever the
//! term, and a dangling address renders as `<dangling>` rather than failing.
//! The walk is a loop over an explicit stack of pieces.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Zone;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_theory_cell_complexes::Polarity;

use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::DestructorTag;
use crate::il::ProducerId;
use crate::il::ProducerNode;

/// Fixed text a rendering writes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Token(&'static str);

/// How deeply a node is nested below the rendered root.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RenderDepth(u32);

impl RenderDepth
{
    /// The root's depth.
    const ROOT: Self = Self(0);
    /// The depth at which a node renders as `…`.
    const LIMIT: Self = Self(64);

    /// The depth of a child.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next depth, saturating at the counter's ceiling.
    /// - provides: one depth step per child edge, without wraparound.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, the penultimate counter and its ceiling have
    ///   exact successors; nested nodes on both sides of the rendering limit
    ///   distinguish a missing step, wraparound and an off-by-one cutoff.
    /// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(1))]
    const fn child(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// Render a command.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the command in the module's notation, depth-bounded, with a
///   dangling address rendered as `<dangling>`.
/// - provides: the textual view of a command.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact finite syntax examples cover each node family, both
///   polarities and argument separators. Dangling addresses and nested nodes
///   immediately below, at and above the depth limit distinguish wrong
///   notation, omitted children and lookup before elision; this is a debug
///   rendering rather than a lossless serialization.
/// - witness: `pretty::tests::renders_terminal_cut`
/// - witness: `pretty::tests::renders_lambda_cocase`
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::literal_spelling_preserves_fraction_and_escaped_content`
#[inline]
#[must_use]
#[spec(ensures: |ref ret| if arena.command(command).is_none() {
    ret == "<dangling>"
} else { ret.starts_with('⟨') && ret.ends_with('⟩') })]
pub fn render_command(
    arena: &CommandArena,
    command: CommandId,
) -> String
{
    render(arena, Piece::Command(command, RenderDepth::ROOT))
}

/// Render a producer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`render_command`], for a producer.
/// - provides: the textual view of a producer.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite constructor, variable and literal syntax is
///   observed exactly; missing producers and the depth boundary distinguish
///   wrong heads, namespaces, escaping and cutoff placement.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::literal_spelling_preserves_fraction_and_escaped_content`
#[inline]
#[must_use]
#[spec(ensures: |ref ret| match arena.producer(producer) {
    | None => ret == "<dangling>",
    | Some(&ProducerNode::Variable { zone, index }) => ret.strip_prefix(match zone {
        | Zone::Intuitionistic => 'x', | Zone::Linear => 'l',
    }).and_then(|digits| digits.parse::<u32>().ok()) == Some(u32::from(index)),
    | Some(&ProducerNode::Constant(index)) => ret.strip_prefix('c').and_then(|digits| digits.parse::<usize>().ok()) == Some(usize::from(index)),
    | Some(_) => true,
})]
pub fn render_producer(
    arena: &CommandArena,
    producer: ProducerId,
) -> String
{
    render(arena, Piece::Producer(producer, RenderDepth::ROOT))
}

/// Render a consumer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`render_command`], for a consumer.
/// - provides: the textual view of a consumer.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact frame and match syntax, empty and multi-arm cases,
///   and missing consumers distinguish wrong separators, binder spelling and
///   omitted continuations; the depth boundary is observed independently of
///   whether an address resolves.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
#[inline]
#[must_use]
#[spec(ensures: |ref ret| match arena.consumer(consumer) {
    | None => ret == "<dangling>",
    | Some(&ConsumerNode::Top) => ret == "★",
    | Some(&ConsumerNode::Covariable(index)) => ret.strip_prefix('α').and_then(|digits| digits.parse::<u32>().ok()) == Some(u32::from(index)),
    | Some(_) => true,
})]
pub fn render_consumer(
    arena: &CommandArena,
    consumer: ConsumerId,
) -> String
{
    render(arena, Piece::Consumer(consumer, RenderDepth::ROOT))
}

/// One pending piece of output.
#[derive(Clone, Debug)]
enum Piece
{
    /// Fixed text.
    Text(Token),
    /// Computed text.
    Owned(String),
    /// A command at a nesting depth.
    Command(CommandId, RenderDepth),
    /// A producer at a nesting depth.
    Producer(ProducerId, RenderDepth),
    /// A consumer at a nesting depth.
    Consumer(ConsumerId, RenderDepth),
}

/// Fixed text as a piece.
macro_rules! text {
    ($fixed:literal) => {
        Piece::Text(Token($fixed))
    };
}

/// Render from a root piece.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every piece is written in order; a node at the depth limit writes
///   `…`.
/// - provides: the one loop every rendering runs.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact nested syntax observes left-to-right output; each
///   node family is elided at the limit before lookup, while missing addresses
///   below it are shown as dangling. Escaped Unicode and control characters
///   distinguish damaged owned text and byte-count mistakes.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::literal_spelling_preserves_fraction_and_escaped_content`
#[spec(
    captures: [fixed = match root { Piece::Text(Token(text)) => Some(text), _ => None },
        owned_length = match root { Piece::Owned(ref text) => Some(text.len()), _ => None },
        elided = matches!(root, Piece::Command(_, depth) | Piece::Producer(_, depth) | Piece::Consumer(_, depth) if depth >= RenderDepth::LIMIT)],
    ensures: |ref ret| fixed.is_none_or(|text| ret == text)
        && owned_length.is_none_or(|length| ret.len() == length) && (!elided || ret == "…"),
)]
fn render(
    arena: &CommandArena,
    root: Piece,
) -> String
{
    let mut out = String::new();
    let mut pending = alloc::vec![root];
    while let Some(piece) = pending.pop() {
        let mut expansion = match piece {
            | Piece::Text(Token(fixed)) => {
                out.push_str(fixed);
                continue;
            },
            | Piece::Owned(computed) => {
                out.push_str(&computed);
                continue;
            },
            | Piece::Command(_, depth) | Piece::Producer(_, depth) | Piece::Consumer(_, depth)
                if depth >= RenderDepth::LIMIT =>
            {
                out.push('…');
                continue;
            },
            | Piece::Command(id, depth) => command(arena, id, depth.child()),
            | Piece::Producer(id, depth) => producer(arena, id, depth.child()),
            | Piece::Consumer(id, depth) => consumer(arena, id, depth.child()),
        };
        expansion.reverse();
        pending.append(&mut expansion);
    }
    out
}

/// The pieces of a command.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a present cut has its two sides at `depth`, delimited by angle
///   brackets and its polarity bar; an absent cut is a dangling marker.
/// - provides: command syntax before recursive child expansion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — positive and negative cuts have exact syntax and distinct
///   sides; a missing cut is a marker and a present cut may contain a dangling
///   child. These distinguish polarity and depth misplacement.
/// - witness: `pretty::tests::renders_terminal_cut`
/// - witness: `pretty::tests::renders_lambda_cocase`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
#[spec(ensures: |ref ret| match (arena.command(id), ret.as_slice()) {
    | (Some(&CommandNode::Cut { polarity, producer, consumer }), &[Piece::Text(Token("⟨")), Piece::Producer(p, pd), Piece::Text(Token(bar)), Piece::Consumer(c, cd), Piece::Text(Token("⟩"))]) =>
        producer == p && consumer == c && pd == depth && cd == depth
            && bar == match polarity { Polarity::Positive => " |+ ", Polarity::Negative => " |− " },
    | (None, &[Piece::Text(Token("<dangling>"))]) => true,
    | _ => false,
})]
fn command(
    arena: &CommandArena,
    id: CommandId,
    depth: RenderDepth,
) -> Vec<Piece>
{
    let Some(&CommandNode::Cut {
        polarity,
        producer,
        consumer,
    }) = arena.command(id)
    else {
        return alloc::vec![text!("<dangling>")];
    };
    let bar = match polarity {
        | Polarity::Positive => " |+ ",
        | Polarity::Negative => " |− ",
    };
    alloc::vec![
        text!("⟨"),
        Piece::Producer(producer, depth),
        Piece::Text(Token(bar)),
        Piece::Consumer(consumer, depth),
        text!("⟩"),
    ]
}

/// The pieces of a producer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: leaf spelling or the producer's head and children in source
///   order, every child scheduled at depth; missing producers are marked.
/// - provides: producer syntax before recursive expansion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — literals, both variable namespaces, constructor fields,
///   captures, thunks and zero-, one- and two-arm copattern objects have exact
///   rendered syntax. The depth boundary distinguishes wrong child depth;
///   missing addresses and unequal fields expose wrong lookup.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::renders_lambda_cocase`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::literal_spelling_preserves_fraction_and_escaped_content`
#[spec(ensures: |ref ret| ret.iter().all(|piece| match *piece {
    | Piece::Command(_, under) | Piece::Producer(_, under) | Piece::Consumer(_, under) => under == depth,
    | Piece::Text(_) | Piece::Owned(_) => true,
}) && match arena.producer(id) {
    | None => matches!(ret.as_slice(), &[Piece::Text(Token("<dangling>"))]),
    | Some(node) => match *node {
        | ProducerNode::Primitive { primitive, .. } => matches!(ret.first(), Some(Piece::Text(Token(name))) if *name == primitive.name().as_ref()),
        | ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Literal(_) => matches!(ret.as_slice(), &[Piece::Owned(_)]),
        | ProducerNode::Constructor { ref tag, ref producers, ref consumers } =>
            if *tag == ConstructorTag::Unit && producers.is_empty() && consumers.is_empty() {
                matches!(ret.as_slice(), &[Piece::Text(Token("()"))])
            } else { matches!(ret.first(), Some(&Piece::Text(Token(name))) if name == constructor_name(tag).0) },
        | ProducerNode::Thunk { body } => matches!(ret.as_slice(), &[Piece::Text(Token("{force(α) ⇒ ")), Piece::Command(found, _), Piece::Text(Token("}"))] if body == found),
        | ProducerNode::Mu { body } => matches!(ret.as_slice(), &[Piece::Text(Token("μα. ")), Piece::Command(found, _)] if body == found),
        | ProducerNode::Cocase { ref arms } => matches!(ret.first(), Some(&Piece::Text(Token("cocase {"))))
            && matches!(ret.last(), Some(&Piece::Text(Token("}"))))
            && ret.iter().filter_map(|piece| match *piece { Piece::Command(body, _) => Some(body), _ => None }).eq(arms.iter().map(|arm| arm.body)),
    },
})]
fn producer(
    arena: &CommandArena,
    id: ProducerId,
    depth: RenderDepth,
) -> Vec<Piece>
{
    let Some(node) = arena.producer(id)
    else {
        return alloc::vec![text!("<dangling>")];
    };
    match *node {
        | ProducerNode::Primitive {
            primitive,
            arguments,
        } => applied(Token(primitive.name().into()), &arguments, &[], depth),
        | ProducerNode::Variable { zone, index } => {
            let prefix = match zone {
                | Zone::Intuitionistic => 'x',
                | Zone::Linear => 'l',
            };
            alloc::vec![Piece::Owned(alloc::format!("{prefix}{}", u32::from(index)))]
        },
        | ProducerNode::Constant(constant) => {
            alloc::vec![Piece::Owned(alloc::format!("c{}", usize::from(constant)))]
        },
        | ProducerNode::Literal(ref literal) => alloc::vec![Piece::Owned(literal_text(literal))],
        | ProducerNode::Constructor {
            ref tag,
            ref producers,
            ref consumers,
        } => {
            if *tag == ConstructorTag::Unit && producers.is_empty() && consumers.is_empty() {
                return alloc::vec![text!("()")];
            }
            applied(constructor_name(tag), producers, consumers, depth)
        },
        | ProducerNode::Thunk { body } => alloc::vec![
            text!("{force(α) ⇒ "),
            Piece::Command(body, depth),
            text!("}"),
        ],
        | ProducerNode::Cocase { ref arms } => {
            let mut pieces = alloc::vec![text!("cocase {")];
            for (position, arm) in arms.iter().enumerate() {
                if position > 0 {
                    pieces.push(text!(" | "));
                }
                pieces.push(Piece::Text(Token(match arm.destructor {
                    | DestructorTag::Apply => "apply(x; α) ⇒ ",
                    | DestructorTag::Force => "force(α) ⇒ ",
                })));
                pieces.push(Piece::Command(arm.body, depth));
            }
            pieces.push(text!("}"));
            pieces
        },
        | ProducerNode::Mu { body } => alloc::vec![text!("μα. "), Piece::Command(body, depth)],
    }
}

/// The pieces of a consumer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the covariable, terminal, binder, destructor or match syntax;
///   children remain in source order at depth, and absent consumers are marked.
/// - provides: consumer syntax before recursive expansion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — terminal and covariable leaves, binders, both destructor
///   heads and empty or multi-arm matches have exact syntax. Distinct fields
///   and depth-limit cases distinguish changed order, wrong head labels and
///   incorrectly scheduled children.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
#[spec(ensures: |ref ret| ret.iter().all(|piece| match *piece {
    | Piece::Command(_, under) | Piece::Producer(_, under) | Piece::Consumer(_, under) => under == depth,
    | Piece::Text(_) | Piece::Owned(_) => true,
}) && match arena.consumer(id) {
    | None => matches!(ret.as_slice(), &[Piece::Text(Token("<dangling>"))]),
    | Some(node) => match *node {
        | ConsumerNode::Covariable(_) => matches!(ret.as_slice(), &[Piece::Owned(_)]),
        | ConsumerNode::Top => matches!(ret.as_slice(), &[Piece::Text(Token("★"))]),
        | ConsumerNode::MuTilde { body } => matches!(ret.as_slice(), &[Piece::Text(Token("μ̃x. ")), Piece::Command(found, _)] if body == found),
        | ConsumerNode::Destructor { tag, .. } => matches!(ret.first(), Some(&Piece::Text(Token(name)))
            if name == match tag { DestructorTag::Apply => "apply", DestructorTag::Force => "force" }),
        | ConsumerNode::Case { ref arms } => matches!(ret.first(), Some(&Piece::Text(Token("case {"))))
            && matches!(ret.last(), Some(&Piece::Text(Token("}"))))
            && ret.iter().filter_map(|piece| match *piece { Piece::Command(body, _) => Some(body), _ => None }).eq(arms.iter().map(|arm| arm.body)),
    },
})]
fn consumer(
    arena: &CommandArena,
    id: ConsumerId,
    depth: RenderDepth,
) -> Vec<Piece>
{
    let Some(node) = arena.consumer(id)
    else {
        return alloc::vec![text!("<dangling>")];
    };
    match *node {
        | ConsumerNode::Covariable(index) => {
            alloc::vec![Piece::Owned(alloc::format!("α{}", u32::from(index)))]
        },
        | ConsumerNode::MuTilde { body } => alloc::vec![text!("μ̃x. "), Piece::Command(body, depth)],
        | ConsumerNode::Destructor {
            tag,
            ref producers,
            ref consumers,
        } => {
            let name = match tag {
                | DestructorTag::Apply => Token("apply"),
                | DestructorTag::Force => Token("force"),
            };
            applied(name, producers, consumers, depth)
        },
        | ConsumerNode::Case { ref arms } => {
            let mut pieces = alloc::vec![text!("case {")];
            for (position, arm) in arms.iter().enumerate() {
                if position > 0 {
                    pieces.push(text!(" | "));
                }
                pieces.push(Piece::Text(pattern_text(&arm.constructor)));
                pieces.push(Piece::Command(arm.body, depth));
            }
            pieces.push(text!("}"));
            pieces
        },
        | ConsumerNode::Top => alloc::vec![text!("★")],
    }
}

/// The pieces of a head applied to producer and consumer children:
/// `name(p, …; c, …)`, the separator present only when both lists are.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the head and parenthesized producer then consumer lists, each in
///   order at depth; commas separate each list and a semicolon separates the
///   lists exactly when both are nonempty.
/// - provides: the shared application notation without hiding invalid arities.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, producer-only, consumer-only and mixed lists with
///   unequal children are rendered exactly. These distinguish missing or extra
///   separators, lost fields, changed order and incorrect depth; arity
///   validation is deliberately outside the debug renderer.
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
#[spec(ensures: |ref ret|
    matches!(ret.first(), Some(&Piece::Text(Token(found))) if found == name.0)
        && matches!(ret.get(1), Some(&Piece::Text(Token("("))))
        && matches!(ret.last(), Some(&Piece::Text(Token(")"))))
        && ret.iter().filter_map(|piece| match *piece { Piece::Producer(id, under) => Some((id, under)), _ => None })
            .eq(producers.iter().copied().map(|id| (id, depth)))
        && ret.iter().filter_map(|piece| match *piece { Piece::Consumer(id, under) => Some((id, under)), _ => None })
            .eq(consumers.iter().copied().map(|id| (id, depth)))
        && ret.iter().skip(2).filter(|piece| matches!(**piece, Piece::Text(Token(", ")))).count()
            == producers.len().saturating_sub(1).saturating_add(consumers.len().saturating_sub(1))
        && ret.iter().skip(2).filter(|piece| matches!(**piece, Piece::Text(Token("; ")))).count()
            == usize::from(!producers.is_empty() && !consumers.is_empty())
)]
fn applied(
    name: Token,
    producers: &[ProducerId],
    consumers: &[ConsumerId],
    depth: RenderDepth,
) -> Vec<Piece>
{
    let mut pieces = alloc::vec![Piece::Text(name), text!("(")];
    for (position, &child) in producers.iter().enumerate() {
        if position > 0 {
            pieces.push(text!(", "));
        }
        pieces.push(Piece::Producer(child, depth));
    }
    if !producers.is_empty() && !consumers.is_empty() {
        pieces.push(text!("; "));
    }
    for (position, &child) in consumers.iter().enumerate() {
        if position > 0 {
            pieces.push(text!(", "));
        }
        pieces.push(Piece::Consumer(child, depth));
    }
    pieces.push(text!(")"));
    pieces
}

/// The name a constructor head renders with.
///
/// # Specification
/// - requires: nothing.
/// - ensures: unit, pair, inl, inr or lift for the corresponding constructor.
/// - provides: the fixed head spelling, independent of a lift's level.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite constructor vocabulary is observed through
///   exact application renderings, including a malformed unit application
///   rather than its nullary abbreviation. This distinguishes swapped labels;
///   no round-trip or parser compatibility is claimed.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
#[spec(ensures: |ret| match *tag {
    | ConstructorTag::Unit => matches!(ret.0.as_bytes(), b"unit"),
    | ConstructorTag::Pair => matches!(ret.0.as_bytes(), b"pair"),
    | ConstructorTag::Injection(Side::Left) => matches!(ret.0.as_bytes(), b"inl"),
    | ConstructorTag::Injection(Side::Right) => matches!(ret.0.as_bytes(), b"inr"),
    | ConstructorTag::Lift(_) => matches!(ret.0.as_bytes(), b"lift"),
})]
const fn constructor_name(tag: &ConstructorTag) -> Token
{
    match *tag {
        | ConstructorTag::Unit => Token("unit"),
        | ConstructorTag::Pair => Token("pair"),
        | ConstructorTag::Injection(Side::Left) => Token("inl"),
        | ConstructorTag::Injection(Side::Right) => Token("inr"),
        | ConstructorTag::Lift(_) => Token("lift"),
    }
}

/// The pattern an arm of a match renders with, its binders unnamed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the constructor's fixed pattern spelling with one unnamed x per
///   producer field, followed by the arm separator.
/// - provides: the binder notation in a match.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every pattern-head kind has an exact rendered arm,
///   covering zero, one and two binders. These distinguish exchanged labels and
///   the wrong binder count within the current vocabulary.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
#[spec(ensures: |ret| match *tag {
    | ConstructorTag::Unit => matches!(ret.0.as_bytes(), b"() \xE2\x87\x92 "),
    | ConstructorTag::Pair => matches!(ret.0.as_bytes(), b"pair(x, x) \xE2\x87\x92 "),
    | ConstructorTag::Injection(Side::Left) => matches!(ret.0.as_bytes(), b"inl(x) \xE2\x87\x92 "),
    | ConstructorTag::Injection(Side::Right) => matches!(ret.0.as_bytes(), b"inr(x) \xE2\x87\x92 "),
    | ConstructorTag::Lift(_) => matches!(ret.0.as_bytes(), b"lift(x) \xE2\x87\x92 "),
})]
const fn pattern_text(tag: &ConstructorTag) -> Token
{
    match *tag {
        | ConstructorTag::Unit => Token("() ⇒ "),
        | ConstructorTag::Pair => Token("pair(x, x) ⇒ "),
        | ConstructorTag::Injection(Side::Left) => Token("inl(x) ⇒ "),
        | ConstructorTag::Injection(Side::Right) => Token("inr(x) ⇒ "),
        | ConstructorTag::Lift(_) => Token("lift(x) ⇒ "),
    }
}

/// A literal's source spelling.
///
/// # Specification
/// - ensures: an integer as its sign and digits, a numeric literal with its
///   fraction, a string quoted with its content escaped.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — integer zero and a negative integer, signed numeric
///   fractions and an empty fraction have exact spellings. Quotes, backslashes,
///   controls and printable Unicode distinguish sign loss, a dropped decimal
///   point, truncation and incorrect escaping.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::literal_spelling_preserves_fraction_and_escaped_content`
#[spec(ensures: |ref ret| match *literal {
    | Literal::Integer(ref integer) => ret.strip_prefix(if integer.sign() == Sign::Negative { "-" } else { "" })
        == Some(integer.magnitude().as_ref()),
    | Literal::Numeric(ref numeric) => ret.strip_prefix(if numeric.sign() == Sign::Negative { "-" } else { "" })
        .and_then(|unsigned| unsigned.split_once('.')).is_some_and(|(whole, fraction)|
            whole == numeric.integer_part().as_ref() && fraction == numeric.fraction().as_ref()),
    | Literal::Text(ref content) => {
        let raw: &str = content.as_ref();
        ret.strip_prefix('"').and_then(|text| text.strip_suffix('"'))
            .is_some_and(|escaped| escaped.chars().eq(raw.chars().flat_map(char::escape_debug)))
    },
})]
fn literal_text(literal: &Literal) -> String
{
    let sign = |sign: Sign| match sign {
        | Sign::Negative => "-",
        | Sign::NonNegative => "",
    };
    match *literal {
        | Literal::Integer(ref integer) => {
            alloc::format!("{}{}", sign(integer.sign()), integer.magnitude().as_ref())
        },
        | Literal::Numeric(ref numeric) => alloc::format!(
            "{}{}.{}",
            sign(numeric.sign()),
            numeric.integer_part().as_ref(),
            numeric.fraction().as_ref()
        ),
        | Literal::Text(ref content) => {
            let mut quoted = String::from("\"");
            let raw: &str = content.as_ref();
            quoted.extend(raw.chars().flat_map(char::escape_debug));
            quoted.push('"');
            quoted
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;

    use gandr_kernel_strata::Level;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Magnitude;

    use super::*;
    use crate::il::CopatternArm;
    use crate::il::CovariableIndex;
    use crate::il::PatternArm;

    /// `⟨() |+ ★⟩` renders as itself.
    #[test]
    fn renders_terminal_cut()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("a leaf mints");
        let top = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let cut = arena
            .mint_cut(Polarity::Positive, unit, top)
            .expect("children resolve");
        assert_eq!("⟨() |+ ★⟩", render_command(&arena, cut), "the terminal cut");
    }

    /// `λ. return x` focused against `★` renders its copattern object at a
    /// negative cut.
    #[test]
    fn renders_lambda_cocase()
    {
        let mut arena = CommandArena::new();
        let variable = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            })
            .expect("a leaf mints");
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
            .expect("a leaf mints");
        let body = arena
            .mint_cut(Polarity::Positive, variable, back)
            .expect("children resolve");
        let object = arena
            .mint_producer(ProducerNode::Cocase {
                arms: Box::from([CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                }]),
            })
            .expect("the body resolves");
        let top = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let cut = arena
            .mint_cut(Polarity::Negative, object, top)
            .expect("children resolve");
        assert_eq!(
            "⟨cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩} |− ★⟩",
            render_command(&arena, cut),
            "the function cut"
        );
    }

    /// Every structural head renders in its notation: the constructors, a
    /// thunk, a capture, the frames, a match, a value binder and a string.
    #[test]
    fn renders_structural_heads()
    {
        let mut arena = CommandArena::new();
        let digits = Magnitude::from_decimal_text(String::from("42")).expect("decimal digits");
        let integer = arena
            .mint_producer(ProducerNode::Literal(Literal::Integer(
                IntegerLiteral::new(Sign::Negative, digits),
            )))
            .expect("a leaf mints");
        let string = arena
            .mint_producer(ProducerNode::Literal(Literal::Text(
                gandr_kernel_term::StringLiteral::new(String::from("a\"b")),
            )))
            .expect("a leaf mints");
        let pair = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Pair,
                producers: Box::from([integer, string]),
                consumers: Box::from([]),
            })
            .expect("fields resolve");
        let right = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Injection(Side::Right),
                producers: Box::from([pair]),
                consumers: Box::from([]),
            })
            .expect("fields resolve");
        let lifted = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Lift(Level::zero()),
                producers: Box::from([right]),
                consumers: Box::from([]),
            })
            .expect("fields resolve");
        assert_eq!(
            "lift(inr(pair(-42, \"a\\\"b\")))",
            render_producer(&arena, lifted),
            "the constructors and literals"
        );

        let top = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let constant = arena
            .mint_producer(ProducerNode::Constant(3_usize.into()))
            .expect("a leaf mints");
        let returned = arena
            .mint_cut(Polarity::Positive, constant, top)
            .expect("children resolve");
        let binder = arena
            .mint_consumer(ConsumerNode::MuTilde { body: returned })
            .expect("the body resolves");
        let apply = arena
            .mint_consumer(ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                producers: Box::from([constant]),
                consumers: Box::from([binder]),
            })
            .expect("children resolve");
        let force = arena
            .mint_consumer(ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([]),
                consumers: Box::from([apply]),
            })
            .expect("children resolve");
        assert_eq!(
            "force(apply(c3; μ̃x. ⟨c3 |+ ★⟩))",
            render_consumer(&arena, force),
            "the frames and the value binder"
        );

        let matcher = arena
            .mint_consumer(ConsumerNode::Case {
                arms: Box::from([
                    PatternArm {
                        constructor: ConstructorTag::Injection(Side::Left),
                        body: returned,
                    },
                    PatternArm {
                        constructor: ConstructorTag::Injection(Side::Right),
                        body: returned,
                    },
                ]),
            })
            .expect("the arms resolve");
        let thunk = arena
            .mint_producer(ProducerNode::Thunk { body: returned })
            .expect("the body resolves");
        let capture = arena
            .mint_producer(ProducerNode::Mu { body: returned })
            .expect("the body resolves");
        let matched = arena
            .mint_cut(Polarity::Positive, thunk, matcher)
            .expect("children resolve");
        let captured = arena
            .mint_cut(Polarity::Positive, capture, top)
            .expect("children resolve");
        assert_eq!(
            "⟨{force(α) ⇒ ⟨c3 |+ ★⟩} |+ case {inl(x) ⇒ ⟨c3 |+ ★⟩ | inr(x) ⇒ ⟨c3 |+ ★⟩}⟩",
            render_command(&arena, matched),
            "the thunk and the match"
        );
        assert_eq!(
            "⟨μα. ⟨c3 |+ ★⟩ |+ ★⟩",
            render_command(&arena, captured),
            "the capture"
        );
        assert_eq!(
            "<dangling>",
            render_command(&arena, CommandId::from(99_u32)),
            "a dangling root"
        );
    }

    /// Elision precedes lookup at the limit, while shallower missing addresses
    /// stay visible.
    #[test]
    fn depth_limits_and_dangling_nodes_are_distinct()
    {
        assert_eq!(RenderDepth(1), RenderDepth::ROOT.child());
        assert_eq!(
            RenderDepth(u32::MAX),
            RenderDepth(u32::MAX.saturating_sub(1)).child()
        );
        assert_eq!(RenderDepth(u32::MAX), RenderDepth(u32::MAX).child());
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let command = arena
            .mint_cut(Polarity::Positive, unit, top)
            .expect("children resolve");
        let missing_producer = ProducerId::from(u32::MAX);
        let missing_consumer = ConsumerId::from(u32::MAX);
        let missing_command = CommandId::from(u32::MAX);
        assert_eq!("<dangling>", render_producer(&arena, missing_producer));
        assert_eq!("<dangling>", render_consumer(&arena, missing_consumer));
        assert_eq!("<dangling>", render_command(&arena, missing_command));
        for piece in [
            Piece::Producer(unit, RenderDepth::LIMIT),
            Piece::Consumer(top, RenderDepth::LIMIT),
            Piece::Command(command, RenderDepth::LIMIT),
            Piece::Producer(missing_producer, RenderDepth::LIMIT),
            Piece::Consumer(missing_consumer, RenderDepth::LIMIT),
            Piece::Command(missing_command, RenderDepth::LIMIT),
        ] {
            assert_eq!("…", render(&arena, piece));
        }
        let below = RenderDepth(RenderDepth::LIMIT.0.saturating_sub(1));
        assert_eq!(
            "<dangling>",
            render(&arena, Piece::Producer(missing_producer, below))
        );
        let limit = usize::try_from(RenderDepth::LIMIT.0).expect("small fixed rendering limit");
        let mut nested = unit;
        for depth in 1_usize ..= limit.saturating_add(1) {
            nested = arena
                .mint_producer(ProducerNode::Constructor {
                    tag: ConstructorTag::Injection(Side::Left),
                    producers: Box::from([nested]),
                    consumers: Box::from([]),
                })
                .expect("child resolves");
            if depth >= limit.saturating_sub(1) {
                let visible = depth.min(limit);
                let leaf = if depth < limit { "()" } else { "…" };
                let expected =
                    alloc::format!("{}{}{}", "inl(".repeat(visible), leaf, ")".repeat(visible));
                assert_eq!(expected, render_producer(&arena, nested));
            }
        }
        let mut broken = CommandArena::new();
        let leaf = broken
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let pair = broken
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Pair,
                producers: Box::from([leaf, leaf]),
                consumers: Box::from([]),
            })
            .expect("children resolve");
        let terminal = broken.mint_consumer(ConsumerNode::Top).expect("leaf");
        let root = broken
            .mint_cut(Polarity::Positive, pair, terminal)
            .expect("children resolve");
        let mut prefix = CommandArena::new();
        let one = prefix
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let end = prefix.mint_consumer(ConsumerNode::Top).expect("leaf");
        prefix
            .mint_cut(Polarity::Positive, one, end)
            .expect("children resolve");
        broken.truncate_to(prefix.watermark());
        assert_eq!("⟨<dangling> |+ ★⟩", render_command(&broken, root));
    }

    /// Unequal children expose punctuation and order in every list and arm
    /// boundary case.
    #[test]
    fn structural_rendering_preserves_fields_arms_and_separators()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let variable = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 7_u32.into(),
            })
            .expect("leaf");
        let linear = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Linear,
                index: 9_u32.into(),
            })
            .expect("leaf");
        assert_eq!("l9", render_producer(&arena, linear));
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let covariable = arena
            .mint_consumer(ConsumerNode::Covariable(1_u32.into()))
            .expect("leaf");
        assert_eq!("α1", render_consumer(&arena, covariable));
        for (producers, consumers, expected) in [
            ([].as_slice(), [].as_slice(), "pair()"),
            ([unit, variable].as_slice(), [].as_slice(), "pair((), x7)"),
            ([].as_slice(), [top, covariable].as_slice(), "pair(★, α1)"),
            (
                [unit, variable].as_slice(),
                [top, covariable].as_slice(),
                "pair((), x7; ★, α1)",
            ),
        ] {
            let producer = arena
                .mint_producer(ProducerNode::Constructor {
                    tag: ConstructorTag::Pair,
                    producers: Box::from(producers),
                    consumers: Box::from(consumers),
                })
                .expect("references resolve even when arity does not");
            assert_eq!(expected, render_producer(&arena, producer));
        }
        let applied_unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([unit]),
                consumers: Box::from([]),
            })
            .expect("child resolves");
        assert_eq!("unit(())", render_producer(&arena, applied_unit));
        let body = arena
            .mint_cut(Polarity::Positive, unit, top)
            .expect("children resolve");
        for (constructor, expected) in [
            (ConstructorTag::Unit, "case {() ⇒ ⟨() |+ ★⟩}"),
            (ConstructorTag::Pair, "case {pair(x, x) ⇒ ⟨() |+ ★⟩}"),
            (
                ConstructorTag::Lift(Level::zero()),
                "case {lift(x) ⇒ ⟨() |+ ★⟩}",
            ),
        ] {
            let matcher = arena
                .mint_consumer(ConsumerNode::Case {
                    arms: Box::from([PatternArm { constructor, body }]),
                })
                .expect("body resolves");
            assert_eq!(expected, render_consumer(&arena, matcher));
        }
        let empty_case = arena
            .mint_consumer(ConsumerNode::Case {
                arms: Box::from([]),
            })
            .expect("empty arms");
        assert_eq!("case {}", render_consumer(&arena, empty_case));
        let empty_object = arena
            .mint_producer(ProducerNode::Cocase {
                arms: Box::from([]),
            })
            .expect("empty arms");
        assert_eq!("cocase {}", render_producer(&arena, empty_object));
        let object = arena
            .mint_producer(ProducerNode::Cocase {
                arms: Box::from([
                    CopatternArm {
                        destructor: DestructorTag::Apply,
                        body,
                    },
                    CopatternArm {
                        destructor: DestructorTag::Force,
                        body,
                    },
                ]),
            })
            .expect("bodies resolve");
        assert_eq!(
            "cocase {apply(x; α) ⇒ ⟨() |+ ★⟩ | force(α) ⇒ ⟨() |+ ★⟩}",
            render_producer(&arena, object)
        );
    }

    /// Numeric fractions and escaped text preserve their payload and kind
    /// distinction.
    #[test]
    fn literal_spelling_preserves_fraction_and_escaped_content()
    {
        use gandr_kernel_term::FractionDigits;
        use gandr_kernel_term::NumericLiteral;
        use gandr_kernel_term::StringLiteral;

        let whole = Magnitude::from_decimal_text(String::from("12")).expect("digits");
        let fraction = FractionDigits::from_decimal_text(String::from("03")).expect("digits");
        for (literal, expected) in [
            (
                Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero())),
                "0",
            ),
            (
                Literal::Numeric(NumericLiteral::new(
                    Sign::NonNegative,
                    whole.clone(),
                    fraction.clone(),
                )),
                "12.03",
            ),
            (
                Literal::Numeric(NumericLiteral::new(Sign::Negative, whole.clone(), fraction)),
                "-12.03",
            ),
            (
                Literal::Numeric(NumericLiteral::new(
                    Sign::NonNegative,
                    whole,
                    FractionDigits::none(),
                )),
                "12.",
            ),
            (
                Literal::Text(StringLiteral::new(String::from("λ\n\t\"\\\0"))),
                r#""λ\n\t\"\\\0""#,
            ),
        ] {
            let mut arena = CommandArena::new();
            let producer = arena
                .mint_producer(ProducerNode::Literal(literal))
                .expect("leaf");
            assert_eq!(expected, render_producer(&arena, producer));
        }
    }
}
