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
    /// The depth past which a node renders as `…`.
    const LIMIT: Self = Self(64);

    /// The depth of a child.
    ///
    /// # Specification
    /// trivial.
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
/// - hypothesis: L3 — a terminal cut, a function cut and the structural heads
///   are pinned to their exact rendering.
/// - witness: `pretty::tests::renders_terminal_cut`
/// - witness: `pretty::tests::renders_lambda_cocase`
/// - witness: `pretty::tests::renders_structural_heads`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — as [`render_command`].
/// - witness: `pretty::tests::renders_structural_heads`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — as [`render_command`].
/// - witness: `pretty::tests::renders_structural_heads`
#[inline]
#[must_use]
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
}
