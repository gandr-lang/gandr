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
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Sign;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::ProducerArity;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::DestructorTag;
use crate::il::Introduces;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::Route;
use crate::il::Selector;

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
///   dangling address rendered as `<dangling>`; a cut, and only a cut, is
///   bracketed `⟨…⟩`, every other command opening with its keyword.
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
#[spec(ensures: |ref ret| match arena.command(command) {
    | None => ret == "<dangling>",
    | Some(&CommandNode::Cut { .. }) => ret.starts_with('⟨') && ret.ends_with('⟩'),
    | Some(_) => !ret.starts_with('⟨'),
})]
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
enum Piece<'arena>
{
    /// An arena-owned name, escaped directly into the output without copying.
    Name(&'arena str),
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
    captures: [fixed = match root { Piece::Text(Token(text)) => Some(text), Piece::Name(_) | Piece::Owned(_) | Piece::Command(..) | Piece::Producer(..) | Piece::Consumer(..) => None },
        owned_length = match root { Piece::Owned(ref text) => Some(text.len()), Piece::Name(_) | Piece::Text(_) | Piece::Command(..) | Piece::Producer(..) | Piece::Consumer(..) => None },
        elided = matches!(root, Piece::Command(_, depth) | Piece::Producer(_, depth) | Piece::Consumer(_, depth) if depth >= RenderDepth::LIMIT)],
    ensures: |ref ret| fixed.is_none_or(|text| ret == text)
        && owned_length.is_none_or(|length| ret.len() == length) && (!elided || ret == "…"),
)]
fn render<'arena>(
    arena: &'arena CommandArena,
    root: Piece<'arena>,
) -> String
{
    let mut out = String::new();
    let mut pending = alloc::vec![root];
    while let Some(piece) = pending.pop() {
        let mut expansion = match piece {
            Piece::Name(name) => {
                out.push('"');
                out.extend(name.escape_debug());
                out.push('"');
                continue;
            },
            Piece::Text(Token(fixed)) => {
                out.push_str(fixed);
                continue;
            },
            Piece::Owned(computed) => {
                out.push_str(&computed);
                continue;
            },
            Piece::Command(_, depth) | Piece::Producer(_, depth) | Piece::Consumer(_, depth)
                if depth >= RenderDepth::LIMIT =>
            {
                out.push('…');
                continue;
            },
            Piece::Command(id, depth) => command(arena, id, depth.child()),
            Piece::Producer(id, depth) => producer(arena, id, depth.child()),
            Piece::Consumer(id, depth) => consumer(arena, id, depth.child()),
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
/// - ensures: every command renders its own instruction and ordered children;
///   an absent command is a dangling marker.
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
/// - witness: `pretty::tests::renders_effect_control_and_memory_commands`
#[spec(ensures: |ref ret| match (arena.command(id), ret.as_slice()) {
    | (Some(&CommandNode::Cut { polarity, producer, consumer }), &[Piece::Text(Token("⟨")), Piece::Producer(p, pd), Piece::Text(Token(bar)), Piece::Consumer(c, cd), Piece::Text(Token("⟩"))]) =>
        producer == p && consumer == c && pd == depth && cd == depth
            && bar == match polarity { Polarity::Positive => " |+ ", Polarity::Negative => " |− " },
    | (None, &[Piece::Text(Token("<dangling>"))]) => true,
    | (Some(&CommandNode::Perform { payload, continuation, .. }), pieces) => pieces.iter().any(|piece| matches!(*piece, Piece::Producer(found, under) if found == payload && under == depth)) && pieces.iter().any(|piece| matches!(*piece, Piece::Consumer(found, under) if found == continuation && under == depth)),
    | (Some(&CommandNode::Handle { subject, on_return, ref clauses, continuation, .. }), pieces) => pieces.iter().filter_map(|piece| match *piece { Piece::Command(id, _) => Some(id), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Producer(..) | Piece::Consumer(..) => None }).eq([subject, on_return].into_iter().chain(clauses.iter().map(|clause| clause.body))) && pieces.iter().any(|piece| matches!(*piece, Piece::Consumer(found, under) if found == continuation && under == depth)),
    | (Some(&CommandNode::Resume { stack, body, continuation }), pieces) => pieces.iter().any(|piece| matches!(*piece, Piece::Producer(found, _) if found == stack)) && pieces.iter().any(|piece| matches!(*piece, Piece::Command(found, under) if found == body && under == depth)) && pieces.iter().any(|piece| matches!(*piece, Piece::Consumer(found, _) if found == continuation)),
    | (Some(&CommandNode::Abandon { stack, continuation }), &[Piece::Text(Token("abandon(")), Piece::Producer(s, sd), Piece::Text(Token("; ")), Piece::Consumer(c, cd), Piece::Text(Token(")"))]) => stack == s && continuation == c && sd == depth && cd == depth,
    | (Some(&CommandNode::Reset { body, continuation } | &CommandNode::Shift { body, continuation }), pieces) => pieces.iter().any(|piece| matches!(*piece, Piece::Command(found, under) if found == body && under == depth)) && pieces.iter().any(|piece| matches!(*piece, Piece::Consumer(found, under) if found == continuation && under == depth)),
    | (Some(&CommandNode::Memory { ref form, continuation }), pieces) => pieces.iter().filter_map(|piece| match *piece { Piece::Command(id, under) if under == depth => Some(id), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Command(..) | Piece::Producer(..) | Piece::Consumer(..) => None }).eq(form.computations()) && pieces.iter().filter_map(|piece| match *piece { Piece::Producer(id, under) if under == depth => Some(id), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Command(..) | Piece::Producer(..) | Piece::Consumer(..) => None }).eq(form.values()) && pieces.iter().any(|piece| matches!(*piece, Piece::Consumer(found, under) if found == continuation && under == depth)),
    | _ => false,
})]
fn command(
    arena: &CommandArena,
    id: CommandId,
    depth: RenderDepth,
) -> Vec<Piece<'_>>
{
    let Some(node) = arena.command(id)
    else {
        return alloc::vec![text!("<dangling>")];
    };
    match *node {
        CommandNode::Cut {
            polarity,
            producer,
            consumer,
        } => alloc::vec![
            text!("⟨"),
            Piece::Producer(producer, depth),
            Piece::Text(Token(match polarity {
                Polarity::Positive => " |+ ",
                Polarity::Negative => " |− ",
            })),
            Piece::Consumer(consumer, depth),
            text!("⟩"),
        ],
        CommandNode::Perform {
            ref signature,
            ref operation,
            route,
            payload,
            continuation,
        } => {
            let mut pieces = Vec::with_capacity(12);
            match route {
                Route::Nearest => pieces.push(text!("perform ")),
                Route::Capability(capability) => pieces.extend([
                    text!("exercise "),
                    Piece::Producer(capability, depth),
                    text!(" "),
                ]),
            }
            pieces.extend([
                Piece::Name(signature.name().as_ref()),
                text!("."),
                Piece::Name(operation.as_ref()),
                text!("("),
                Piece::Producer(payload, depth),
                text!("; "),
                Piece::Consumer(continuation, depth),
                text!(")"),
            ]);
            pieces
        },
        CommandNode::Handle {
            ref signature,
            introduces,
            subject,
            on_return,
            ref clauses,
            continuation,
        } => {
            let mut pieces = Vec::with_capacity(clauses.len().saturating_mul(4).saturating_add(8));
            pieces.extend([
                match introduces {
                    Introduces::Nothing => text!("handle "),
                    Introduces::Capability => text!("scope "),
                },
                Piece::Name(signature.name().as_ref()),
                match introduces {
                    Introduces::Nothing => text!(" { "),
                    Introduces::Capability => text!(" { (c) ⇒ "),
                },
                Piece::Command(subject, depth),
                text!(" | return(x; α) ⇒ "),
                Piece::Command(on_return, depth),
            ]);
            for clause in clauses.iter() {
                pieces.extend([
                    text!(" | "),
                    Piece::Name(clause.operation.as_ref()),
                    text!("(payload, k; α) ⇒ "),
                    Piece::Command(clause.body, depth),
                ]);
            }
            pieces.extend([text!(" }; "), Piece::Consumer(continuation, depth)]);
            pieces
        },
        CommandNode::Resume {
            stack,
            body,
            continuation,
        } => alloc::vec![
            text!("resume("),
            Piece::Producer(stack, depth),
            text!("; "),
            Piece::Command(body, depth),
            text!("; "),
            Piece::Consumer(continuation, depth),
            text!(")")
        ],
        CommandNode::Abandon {
            stack,
            continuation,
        } => alloc::vec![
            text!("abandon("),
            Piece::Producer(stack, depth),
            text!("; "),
            Piece::Consumer(continuation, depth),
            text!(")")
        ],
        CommandNode::Reset { body, continuation } => alloc::vec![
            text!("reset("),
            Piece::Command(body, depth),
            text!("; "),
            Piece::Consumer(continuation, depth),
            text!(")")
        ],
        CommandNode::Shift { body, continuation } => alloc::vec![
            text!("shift(k; "),
            Piece::Command(body, depth),
            text!("; "),
            Piece::Consumer(continuation, depth),
            text!(")")
        ],
        CommandNode::Memory {
            ref form,
            continuation,
        } => {
            let linear =
                |index: DeBruijnIndex| Piece::Owned(alloc::format!("l{}", u32::from(index)));
            let mut pieces = match *form {
                MemoryForm::Hold {
                    value,
                    body,
                    grade: gandr_core_term::memory::HoldGrade::Many,
                } => alloc::vec![
                    text!("hold("),
                    Piece::Producer(value, depth),
                    text!("; (l; α) ⇒ "),
                    Piece::Command(body, depth),
                ],
                MemoryForm::Hold {
                    value,
                    body,
                    grade: gandr_core_term::memory::HoldGrade::One,
                } => alloc::vec![
                    text!("hold[1]("),
                    Piece::Producer(value, depth),
                    text!("; (l; α) ⇒ "),
                    Piece::Command(body, depth),
                ],
                MemoryForm::Access {
                    mode,
                    held,
                    place,
                    body,
                } => {
                    let mut access = alloc::vec![
                        match mode {
                            AccessMode::Exclusive { .. } => text!("access("),
                            AccessMode::Shared => text!("access_shared("),
                        },
                        linear(held),
                    ];
                    if let Place::At { index } = place {
                        access.extend([text!("["), Piece::Producer(index, depth), text!("]")]);
                    }
                    access.extend([text!("; (l; α) ⇒ "), Piece::Command(body, depth)]);
                    if let AccessMode::Exclusive { unwind } = mode {
                        access.extend([text!(" | unwind(α) ⇒ "), Piece::Command(unwind, depth)]);
                    }
                    access
                },
                MemoryForm::Resume { view, value } => alloc::vec![
                    text!("writeback("),
                    linear(view),
                    text!(", "),
                    Piece::Producer(value, depth),
                ],
                MemoryForm::Abort { view } => alloc::vec![text!("abort("), linear(view)],
                MemoryForm::Consume { held } => alloc::vec![text!("consume("), linear(held)],
            };
            pieces.extend([
                text!("; "),
                Piece::Consumer(continuation, depth),
                text!(")"),
            ]);
            pieces
        },
    }
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
///   datatype ordinals, captures, thunks, recursive thunks under both evidences
///   and zero-, one- and two-arm copattern objects have exact rendered syntax.
///   The depth boundary distinguishes wrong child depth; missing addresses and
///   unequal fields expose wrong lookup.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::renders_datatype_heads_nominal_matches_and_recursive_thunks`
/// - witness: `pretty::tests::renders_lambda_cocase`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::literal_spelling_preserves_fraction_and_escaped_content`
/// - witness: `pretty::tests::renders_frames_primitives_folds_and_projections`
#[spec(ensures: |ref ret| ret.iter().all(|piece| match *piece {
    | Piece::Command(_, under) | Piece::Producer(_, under) | Piece::Consumer(_, under) => under == depth,
    | Piece::Text(_) | Piece::Owned(_) | Piece::Name(_) => true,
}) && match arena.producer(id) {
    | None => matches!(ret.as_slice(), &[Piece::Text(Token("<dangling>"))]),
    | Some(node) => match *node {
        | ProducerNode::Reify(_) => matches!(ret.first(), Some(Piece::Text(Token("reify [")))) && matches!(ret.last(), Some(Piece::Text(Token("]")))),
        | ProducerNode::Primitive { primitive, .. } => matches!(ret.first(), Some(Piece::Text(Token(name))) if *name == primitive.name().as_ref()),
        | ProducerNode::Decompose(_) => matches!(ret.first(), Some(Piece::Text(Token("decompose")))),
        | ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Literal(_) => matches!(ret.as_slice(), &[Piece::Owned(_)]),
        | ProducerNode::Code(_) => matches!(ret.as_slice(), &[Piece::Text(Token("code"))]),
        | ProducerNode::Constructor { ref tag, ref producers, ref consumers } =>
            if *tag == ConstructorTag::Tuple(ProducerArity::ZERO) && producers.is_empty() && consumers.is_empty() {
                matches!(ret.as_slice(), &[Piece::Text(Token("()"))])
            } else { matches!(ret.first(), Some(&Piece::Text(Token(name))) if name == constructor_name(tag).0) },
        | ProducerNode::Thunk { body } => matches!(ret.as_slice(), &[Piece::Text(Token("{force(α) ⇒ ")), Piece::Command(found, _), Piece::Text(Token("}"))] if body == found),
        | ProducerNode::Fixpoint { body, .. } => matches!(ret.as_slice(), &[Piece::Text(Token("fix")), Piece::Text(_) | Piece::Owned(_), Piece::Command(found, _), Piece::Text(Token("}"))] if body == found),
        | ProducerNode::Mu { body } => matches!(ret.as_slice(), &[Piece::Text(Token("μα. ")), Piece::Command(found, _)] if body == found),
        | ProducerNode::Cocase { ref arms } => matches!(ret.first(), Some(&Piece::Text(Token("cocase {"))))
            && matches!(ret.last(), Some(&Piece::Text(Token("}"))))
            && ret.iter().filter_map(|piece| match *piece { Piece::Command(body, _) => Some(body), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Producer(..) | Piece::Consumer(..) => None }).eq(arms.iter().map(|arm| arm.body)),
    },
})]
fn producer(
    arena: &CommandArena,
    id: ProducerId,
    depth: RenderDepth,
) -> Vec<Piece<'_>>
{
    let Some(node) = arena.producer(id)
    else {
        return alloc::vec![text!("<dangling>")];
    };
    match *node {
        ProducerNode::Reify(ref frames) => {
            let mut pieces = Vec::with_capacity(frames.len().saturating_mul(4).saturating_add(2));
            pieces.push(text!("reify ["));
            for (index, frame) in frames.iter().enumerate() {
                if index > 0 {
                    pieces.push(text!("; "));
                }
                match *frame {
                    gandr_core_term::control::StackFrame::Apply(value) => {
                        pieces.extend([text!("apply("), Piece::Producer(value, depth), text!(")")]);
                    },
                    gandr_core_term::control::StackFrame::Bind(body) => {
                        pieces.extend([text!("bind(x; α) ⇒ "), Piece::Command(body, depth)]);
                    },
                    gandr_core_term::control::StackFrame::Project(component) => {
                        pieces.push(Piece::Owned(alloc::format!(
                            "project[{}]",
                            usize::from(component)
                        )));
                    },
                }
            }
            pieces.push(text!("]"));
            pieces
        },
        ProducerNode::Primitive {
            primitive,
            arguments,
        } => applied(Token(primitive.name().into()), &arguments, &[], depth),
        ProducerNode::Decompose(dialogue) => applied(Token("decompose"), &[dialogue], &[], depth),
        ProducerNode::Variable { zone, index } => {
            let prefix = match zone {
                Zone::Intuitionistic => 'x',
                Zone::Linear => 'l',
            };
            alloc::vec![Piece::Owned(alloc::format!("{prefix}{}", u32::from(index)))]
        },
        ProducerNode::Constant(constant) => {
            alloc::vec![Piece::Owned(alloc::format!("c{}", usize::from(constant)))]
        },
        ProducerNode::Literal(ref literal) => alloc::vec![Piece::Owned(literal_text(literal))],
        ProducerNode::Code(_) => alloc::vec![text!("code")],
        ProducerNode::Constructor {
            ref tag,
            ref producers,
            ref consumers,
        } => {
            if *tag == ConstructorTag::Tuple(ProducerArity::ZERO)
                && producers.is_empty()
                && consumers.is_empty()
            {
                return alloc::vec![text!("()")];
            }
            let mut pieces = applied(constructor_name(tag), producers, consumers, depth);
            if let Some(position) = qualifier(tag) {
                pieces.insert(1, position);
            }
            pieces
        },
        ProducerNode::Thunk { body } => alloc::vec![
            text!("{force(α) ⇒ "),
            Piece::Command(body, depth),
            text!("}"),
        ],
        ProducerNode::Fixpoint { body, evidence } => alloc::vec![
            text!("fix"),
            match evidence {
                FixpointEvidence::Partial => text!("{x; force(α) ⇒ "),
                FixpointEvidence::StructuralDescent => text!("[<]{x; force(α) ⇒ "),
                FixpointEvidence::Staged { position } => Piece::Owned(alloc::format!(
                    "[<{}]{{x; force(α) ⇒ ",
                    usize::from(position)
                )),
            },
            Piece::Command(body, depth),
            text!("}"),
        ],
        ProducerNode::Cocase { ref arms } => {
            let mut pieces = alloc::vec![text!("cocase {")];
            for (position, arm) in arms.iter().enumerate() {
                if position > 0 {
                    pieces.push(text!(" | "));
                }
                pieces.push(match arm.destructor {
                    DestructorTag::Apply => text!("apply(x; α) ⇒ "),
                    DestructorTag::Force => text!("force(α) ⇒ "),
                    DestructorTag::Project(component) => {
                        Piece::Owned(alloc::format!("project[{}](α) ⇒ ", usize::from(component)))
                    },
                });
                pieces.push(Piece::Command(arm.body, depth));
            }
            pieces.push(text!("}"));
            pieces
        },
        ProducerNode::Mu { body } => alloc::vec![text!("μα. "), Piece::Command(body, depth)],
    }
}

/// The pieces of a consumer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the covariable, terminal, binder, destructor, match, nominal
///   match or selection syntax; children remain in source order at depth, and
///   absent consumers are marked.
/// - provides: consumer syntax before recursive expansion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — terminal and covariable leaves, binders, both destructor
///   heads, empty or multi-arm matches and a nominal match's branches and
///   continuation have exact syntax. Distinct fields and depth-limit cases
///   distinguish changed order, wrong head labels and incorrectly scheduled
///   children.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::renders_datatype_heads_nominal_matches_and_recursive_thunks`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::renders_records_and_selections`
/// - witness: `pretty::tests::renders_frames_primitives_folds_and_projections`
#[spec(ensures: |ref ret| ret.iter().all(|piece| match *piece {
    | Piece::Command(_, under) | Piece::Producer(_, under) | Piece::Consumer(_, under) => under == depth,
    | Piece::Text(_) | Piece::Owned(_) | Piece::Name(_) => true,
}) && match arena.consumer(id) {
    | None => matches!(ret.as_slice(), &[Piece::Text(Token("<dangling>"))]),
    | Some(node) => match *node {
        | ConsumerNode::Covariable(_) => matches!(ret.as_slice(), &[Piece::Owned(_)]),
        | ConsumerNode::Top => matches!(ret.as_slice(), &[Piece::Text(Token("★"))]),
        | ConsumerNode::ListFold { on_nil, on_cons, continuation, .. } => ret.iter().filter_map(|piece| match *piece { Piece::Command(body, _) => Some(body), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Producer(..) | Piece::Consumer(..) => None }).eq([on_nil, on_cons]) && ret.iter().any(|piece| matches!(*piece, Piece::Consumer(found, _) if found == continuation)),
        | ConsumerNode::MuTilde { body } => matches!(ret.as_slice(), &[Piece::Text(Token("μ̃x. ")), Piece::Command(found, _)] if body == found),
        | ConsumerNode::Destructor { tag, .. } => matches!(ret.first(), Some(&Piece::Text(Token(name)))
            if name == match tag { DestructorTag::Apply => "apply", DestructorTag::Force => "force", DestructorTag::Project(_) => "project" })
            && match tag {
                | DestructorTag::Project(component) => matches!(ret.get(1), Some(&Piece::Owned(ref index)) if *index == alloc::format!("[{}]", usize::from(component))),
                | DestructorTag::Apply | DestructorTag::Force => true,
            },
        | ConsumerNode::Case { ref arms } => matches!(ret.first(), Some(&Piece::Text(Token("case {"))))
            && matches!(ret.last(), Some(&Piece::Text(Token("}"))))
            && ret.iter().filter_map(|piece| match *piece { Piece::Command(body, _) => Some(body), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Producer(..) | Piece::Consumer(..) => None }).eq(arms.iter().map(|arm| arm.body)),
        | ConsumerNode::DataCase { ref branches, then, .. } => matches!(ret.first(), Some(&Piece::Text(Token("datacase"))))
            && ret.iter().filter_map(|piece| match *piece { Piece::Producer(id, _) => Some(id), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Command(..) | Piece::Consumer(..) => None }).eq(branches.iter().copied())
            && ret.iter().filter_map(|piece| match *piece { Piece::Consumer(id, _) => Some(id), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Command(..) | Piece::Producer(..) => None }).eq(core::iter::once(then)),
        | ConsumerNode::Select { ref selector, then } => matches!(ret.as_slice(), &[Piece::Text(Token("select")), Piece::Owned(ref field), Piece::Text(Token("(")), Piece::Consumer(found, _), Piece::Text(Token(")"))]
            if found == then && *field == match *selector {
                | Selector::Component(component) => alloc::format!("[{}]", usize::from(component)),
                | Selector::Label(ref label) => alloc::format!("[.{}]", label.as_ref()),
            }),
    },
})]
fn consumer(
    arena: &CommandArena,
    id: ConsumerId,
    depth: RenderDepth,
) -> Vec<Piece<'_>>
{
    let Some(node) = arena.consumer(id)
    else {
        return alloc::vec![text!("<dangling>")];
    };
    match *node {
        ConsumerNode::Covariable(index) => {
            alloc::vec![Piece::Owned(alloc::format!("α{}", u32::from(index)))]
        },
        ConsumerNode::MuTilde { body } => alloc::vec![text!("μ̃x. "), Piece::Command(body, depth)],
        ConsumerNode::ListFold {
            on_nil,
            on_cons,
            continuation,
            ..
        } => alloc::vec![
            text!("fold {nil ⇒ "),
            Piece::Command(on_nil, depth),
            text!(" | cons(head, result) ⇒ "),
            Piece::Command(on_cons, depth),
            text!("}; "),
            Piece::Consumer(continuation, depth)
        ],
        ConsumerNode::Destructor {
            tag,
            ref producers,
            ref consumers,
        } => {
            let name = match tag {
                DestructorTag::Apply => Token("apply"),
                DestructorTag::Force => Token("force"),
                DestructorTag::Project(_) => Token("project"),
            };
            let mut pieces = applied(name, producers, consumers, depth);
            if let DestructorTag::Project(component) = tag {
                pieces.insert(
                    1,
                    Piece::Owned(alloc::format!("[{}]", usize::from(component))),
                );
            }
            pieces
        },
        ConsumerNode::DataCase {
            ref branches, then, ..
        } => applied(
            Token("datacase"),
            branches,
            core::slice::from_ref(&then),
            depth,
        ),
        ConsumerNode::Select { ref selector, then } => {
            let mut pieces = applied(Token("select"), &[], core::slice::from_ref(&then), depth);
            let field = match *selector {
                Selector::Component(component) => {
                    alloc::format!("[{}]", usize::from(component))
                },
                Selector::Label(ref label) => alloc::format!("[.{}]", label.as_ref()),
            };
            pieces.insert(1, Piece::Owned(field));
            pieces
        },
        ConsumerNode::Case { ref arms } => {
            let mut pieces = alloc::vec![text!("case {")];
            for (position, arm) in arms.iter().enumerate() {
                if position > 0 {
                    pieces.push(text!(" | "));
                }
                pieces.push(pattern(&arm.constructor));
                pieces.push(Piece::Command(arm.body, depth));
            }
            pieces.push(text!("}"));
            pieces
        },
        ConsumerNode::Top => alloc::vec![text!("★")],
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
        && ret.iter().filter_map(|piece| match *piece { Piece::Producer(id, under) => Some((id, under)), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Command(..) | Piece::Consumer(..) => None })
            .eq(producers.iter().copied().map(|id| (id, depth)))
        && ret.iter().filter_map(|piece| match *piece { Piece::Consumer(id, under) => Some((id, under)), Piece::Name(_) | Piece::Text(_) | Piece::Owned(_) | Piece::Command(..) | Piece::Producer(..) => None })
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
) -> Vec<Piece<'static>>
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
/// - ensures: unit for the empty tuple, pair for a tuple of two, tuple for any
///   other; record for a record; inl and inr for the first two summands, inj
///   past them; nil, cons, lift, ctor, recorded, dialogue or web for the
///   corresponding constructor.
/// - provides: the fixed head spelling, independent of a lift's level; a
///   datatype constructor's ordinal, a record's labels, a recorded run's or a
///   dialogue's moves, a web's pieces and a summand past the second are written
///   after it by the caller.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite constructor vocabulary is observed through
///   exact application renderings, including a malformed unit application
///   rather than its nullary abbreviation and a tuple and an injection past the
///   binary ones. This distinguishes swapped labels; no round-trip or parser
///   compatibility is claimed.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::renders_datatype_heads_nominal_matches_and_recursive_thunks`
/// - witness: `pretty::tests::depth_limits_and_dangling_nodes_are_distinct`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
#[spec(ensures: |ret| match *tag {
    | ConstructorTag::Tuple(ProducerArity::ZERO) => matches!(ret.0.as_bytes(), b"unit"),
    | ConstructorTag::Tuple(ProducerArity::TWO) => matches!(ret.0.as_bytes(), b"pair"),
    | ConstructorTag::Tuple(_) => matches!(ret.0.as_bytes(), b"tuple"),
    | ConstructorTag::Record(_) => matches!(ret.0.as_bytes(), b"record"),
    | ConstructorTag::ListNil => matches!(ret.0.as_bytes(), b"nil"),
    | ConstructorTag::ListCons => matches!(ret.0.as_bytes(), b"cons"),
    | ConstructorTag::Injection(summand) => match usize::from(summand) {
        | 0 => matches!(ret.0.as_bytes(), b"inl"),
        | 1 => matches!(ret.0.as_bytes(), b"inr"),
        | _ => matches!(ret.0.as_bytes(), b"inj"),
    },
    | ConstructorTag::Lift(_) => matches!(ret.0.as_bytes(), b"lift"),
    | ConstructorTag::Data { .. } => matches!(ret.0.as_bytes(), b"ctor"),
    | ConstructorTag::Recorded(_) => matches!(ret.0.as_bytes(), b"recorded"),
    | ConstructorTag::Dialogue(_) => matches!(ret.0.as_bytes(), b"dialogue"),
    | ConstructorTag::Web(_) => matches!(ret.0.as_bytes(), b"web"),
})]
fn constructor_name(tag: &ConstructorTag) -> Token
{
    match *tag {
        ConstructorTag::Tuple(ProducerArity::ZERO) => Token("unit"),
        ConstructorTag::Tuple(ProducerArity::TWO) => Token("pair"),
        ConstructorTag::Tuple(_) => Token("tuple"),
        ConstructorTag::Record(_) => Token("record"),
        ConstructorTag::ListNil => Token("nil"),
        ConstructorTag::ListCons => Token("cons"),
        ConstructorTag::Injection(summand) => match usize::from(summand) {
            0 => Token("inl"),
            1 => Token("inr"),
            _ => Token("inj"),
        },
        ConstructorTag::Lift(_) => Token("lift"),
        ConstructorTag::Data { .. } => Token("ctor"),
        ConstructorTag::Recorded(_) => Token("recorded"),
        ConstructorTag::Dialogue(_) => Token("dialogue"),
        ConstructorTag::Web(_) => Token("web"),
    }
}

/// The position a head's name is qualified by: a datatype constructor's
/// ordinal, a record's labels, a recorded run's or a dialogue's moves, a
/// web's pieces and a summand past the second.
///
/// # Specification
/// trivial.
fn qualifier(tag: &ConstructorTag) -> Option<Piece<'static>>
{
    match *tag {
        ConstructorTag::Data { tag: ordinal, .. } => {
            Some(Piece::Owned(alloc::format!("[{}]", usize::from(ordinal))))
        },
        ConstructorTag::Injection(summand) if usize::from(summand) > 1 => {
            Some(Piece::Owned(alloc::format!("[{}]", usize::from(summand))))
        },
        ConstructorTag::Record(ref labels) => Some(Piece::Owned(labels_spelled(labels))),
        ConstructorTag::Recorded(ref moves) => Some(Piece::Owned(moves_spelled(moves))),
        ConstructorTag::Dialogue(ref turns) => Some(Piece::Owned(turns_spelled(turns))),
        ConstructorTag::Web(ref pieces) => Some(Piece::Owned(pieces_spelled(pieces))),
        ConstructorTag::Tuple(_)
        | ConstructorTag::ListNil
        | ConstructorTag::ListCons
        | ConstructorTag::Injection(_)
        | ConstructorTag::Lift(_) => None,
    }
}

/// The pattern an arm of a match renders with, its binders unnamed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the constructor's pattern spelling with one unnamed x per
///   producer field, followed by the arm separator; a datatype constructor and
///   a summand past the second write their position.
/// - provides: the binder notation in a match.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every pattern-head kind has an exact rendered arm,
///   covering zero, one, two and three binders, a datatype ordinal and a third
///   summand. These distinguish exchanged labels and the wrong binder count
///   within the current vocabulary.
/// - witness: `pretty::tests::renders_structural_heads`
/// - witness: `pretty::tests::renders_datatype_heads_nominal_matches_and_recursive_thunks`
/// - witness: `pretty::tests::structural_rendering_preserves_fields_arms_and_separators`
#[spec(ensures: |ref ret| match (tag, ret) {
    | (&ConstructorTag::Tuple(ProducerArity::ZERO), &Piece::Text(Token(text))) => text == "() ⇒ ",
    | (&ConstructorTag::Tuple(ProducerArity::TWO), &Piece::Text(Token(text))) => text == "pair(x, x) ⇒ ",
    | (&ConstructorTag::Tuple(arity), &Piece::Owned(ref text)) =>
        text.starts_with("tuple(") && text.matches('x').count() == usize::from(arity),
    | (&ConstructorTag::Record(ref labels), &Piece::Owned(ref text)) =>
        *text == alloc::format!("record{}({}) ⇒ ", labels_spelled(labels), alloc::vec!["x"; labels.len()].join(", ")),
    | (&ConstructorTag::ListNil, &Piece::Text(Token(text))) => text == "nil ⇒ ",
    | (&ConstructorTag::ListCons, &Piece::Text(Token(text))) => text == "cons(x, x) ⇒ ",
    | (&ConstructorTag::Injection(summand), &Piece::Text(Token(text))) => match usize::from(summand) {
        | 0 => text == "inl(x) ⇒ ",
        | 1 => text == "inr(x) ⇒ ",
        | _ => false,
    },
    | (&ConstructorTag::Injection(summand), &Piece::Owned(ref text)) =>
        *text == alloc::format!("inj[{}](x) ⇒ ", usize::from(summand)),
    | (&ConstructorTag::Lift(_), &Piece::Text(Token(text))) => text == "lift(x) ⇒ ",
    | (&ConstructorTag::Data { tag: ordinal, arity, .. }, &Piece::Owned(ref text)) =>
        text.starts_with(&alloc::format!("ctor[{}](", usize::from(ordinal)))
            && text.matches('x').count() == usize::from(arity),
    | (&ConstructorTag::Recorded(ref moves), &Piece::Owned(ref text)) =>
        *text == alloc::format!("recorded{}({}) ⇒ ", moves_spelled(moves), alloc::vec!["x"; usize::from(tag.producer_arity())].join(", ")),
    | (&ConstructorTag::Dialogue(ref turns), &Piece::Owned(ref text)) =>
        *text == alloc::format!("dialogue{}({}) ⇒ ", turns_spelled(turns), alloc::vec!["x"; usize::from(tag.producer_arity())].join(", ")),
    | (&ConstructorTag::Web(ref pieces), &Piece::Owned(ref text)) =>
        *text == alloc::format!("web{} ⇒ ", pieces_spelled(pieces)),
    | _ => false,
})]
fn pattern(tag: &ConstructorTag) -> Piece<'static>
{
    match *tag {
        ConstructorTag::Tuple(ProducerArity::ZERO) => text!("() ⇒ "),
        ConstructorTag::Tuple(ProducerArity::TWO) => text!("pair(x, x) ⇒ "),
        ConstructorTag::Tuple(arity) => {
            let binders = alloc::vec!["x"; usize::from(arity)].join(", ");
            Piece::Owned(alloc::format!("tuple({binders}) ⇒ "))
        },
        ConstructorTag::Record(ref labels) => {
            let binders = alloc::vec!["x"; labels.len()].join(", ");
            Piece::Owned(alloc::format!(
                "record{}({binders}) ⇒ ",
                labels_spelled(labels)
            ))
        },
        ConstructorTag::ListNil => text!("nil ⇒ "),
        ConstructorTag::ListCons => text!("cons(x, x) ⇒ "),
        ConstructorTag::Injection(summand) => match usize::from(summand) {
            0 => text!("inl(x) ⇒ "),
            1 => text!("inr(x) ⇒ "),
            position => Piece::Owned(alloc::format!("inj[{position}](x) ⇒ ")),
        },
        ConstructorTag::Lift(_) => text!("lift(x) ⇒ "),
        ConstructorTag::Data {
            tag: ordinal,
            arity,
            ..
        } => {
            let binders = alloc::vec!["x"; usize::from(arity)].join(", ");
            Piece::Owned(alloc::format!(
                "ctor[{}]({binders}) ⇒ ",
                usize::from(ordinal)
            ))
        },
        ConstructorTag::Recorded(ref moves) => {
            let binders = alloc::vec!["x"; usize::from(tag.producer_arity())].join(", ");
            Piece::Owned(alloc::format!(
                "recorded{}({binders}) ⇒ ",
                moves_spelled(moves)
            ))
        },
        ConstructorTag::Dialogue(ref turns) => {
            let binders = alloc::vec!["x"; usize::from(tag.producer_arity())].join(", ");
            Piece::Owned(alloc::format!(
                "dialogue{}({binders}) ⇒ ",
                turns_spelled(turns)
            ))
        },
        ConstructorTag::Web(ref pieces) => {
            Piece::Owned(alloc::format!("web{} ⇒ ", pieces_spelled(pieces)))
        },
    }
}

/// One recorded move: `sent`, `received`, `selected(l)`, `offered(l)` or
/// `closed`.
///
/// # Specification
/// trivial.
fn move_spelled(movement: &gandr_core_term::session::RecordedMove<()>) -> String
{
    use gandr_core_term::session::RecordedMove;
    match *movement {
        RecordedMove::Sent(()) => String::from("sent"),
        RecordedMove::Received(()) => String::from("received"),
        RecordedMove::Selected(ref label) => alloc::format!("selected({})", label.as_ref()),
        RecordedMove::Offered(ref label) => alloc::format!("offered({})", label.as_ref()),
        RecordedMove::Closed => String::from("closed"),
    }
}

/// A recorded run head's moves, in order, between brackets: `[sent,
/// selected(l), closed]`.
///
/// # Specification
/// trivial.
fn moves_spelled(moves: &[gandr_core_term::session::RecordedMove<()>]) -> String
{
    let spelled: Vec<String> = moves.iter().map(move_spelled).collect();
    alloc::format!("[{}]", spelled.join(", "))
}

/// A dialogue head's moves, in log order, each under its endpoint, between
/// brackets: `[left(sent), right(received)]`.
///
/// # Specification
/// trivial.
fn turns_spelled(turns: &[gandr_core_term::session::DialogueMove<()>]) -> String
{
    use gandr_core_term::session::Endpoint;
    let spelled: Vec<String> = turns
        .iter()
        .map(|turn| {
            let endpoint = match turn.endpoint {
                Endpoint::Left => "left",
                Endpoint::Right => "right",
            };
            alloc::format!("{endpoint}({})", move_spelled(&turn.movement))
        })
        .collect();
    alloc::format!("[{}]", spelled.join(", "))
}

/// A web head's pieces, in preorder, between brackets: `[series(2),
/// event(left, 0), event(right, 0)]`.
///
/// # Specification
/// trivial.
fn pieces_spelled(pieces: &[gandr_core_term::session::WebPiece]) -> String
{
    use gandr_core_term::session::Endpoint;
    use gandr_core_term::session::WebPiece;
    let spelled: Vec<String> = pieces
        .iter()
        .map(|piece| match *piece {
            WebPiece::Event { endpoint, index } => {
                let endpoint = match endpoint {
                    Endpoint::Left => "left",
                    Endpoint::Right => "right",
                };
                alloc::format!("event({endpoint}, {index})")
            },
            WebPiece::Series(factors) => alloc::format!("series({factors})"),
            WebPiece::Parallel(factors) => alloc::format!("parallel({factors})"),
            WebPiece::Prime(factors) => alloc::format!("prime({factors})"),
        })
        .collect();
    alloc::format!("[{}]", spelled.join(", "))
}

/// A record head's labels, in its order, between braces: `{a, b}`.
///
/// # Specification
/// trivial.
fn labels_spelled(labels: &[gandr_core_term::FieldLabel]) -> alloc::string::String
{
    let spelled: Vec<&str> = labels.iter().map(AsRef::as_ref).collect();
    alloc::format!("{{{}}}", spelled.join(", "))
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
        Sign::Negative => "-",
        Sign::NonNegative => "",
    };
    match *literal {
        Literal::Integer(ref integer) => {
            alloc::format!("{}{}", sign(integer.sign()), integer.magnitude().as_ref())
        },
        Literal::Numeric(ref numeric) => alloc::format!(
            "{}{}.{}",
            sign(numeric.sign()),
            numeric.integer_part().as_ref(),
            numeric.fraction().as_ref()
        ),
        Literal::Text(ref content) => {
            let mut quoted = String::from("\"");
            let raw: &str = content.as_ref();
            quoted.extend(raw.chars().flat_map(char::escape_debug));
            quoted.push('"');
            quoted
        },
    }
}

#[cfg(test)]
mod tests;
