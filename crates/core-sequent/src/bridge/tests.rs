use gandr_kernel_term::Side;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::ProdPat;

use super::*;
use crate::boundary::NodeCount;
use crate::check::FreeSet;
use crate::check::check_command;
use crate::pretty::render_command;

/// The core's own constructors under the names a test pattern uses.
///
/// # Specification
/// trivial.
fn core_resolver() -> ConstructorResolver
{
    let mut resolver = ConstructorResolver::new();
    resolver.insert(Sym::new("Unit"), ConstructorTag::Tuple(ProducerArity::ZERO));
    resolver.insert(Sym::new("Pair"), ConstructorTag::Tuple(ProducerArity::TWO));
    resolver.insert(
        Sym::new("Inl"),
        ConstructorTag::Injection(Side::Left.into()),
    );
    resolver.insert(
        Sym::new("Inr"),
        ConstructorTag::Injection(Side::Right.into()),
    );
    resolver
}

/// `⟨Pair(Unit, Inl(Unit)) |+ ★⟩` reifies node for node and passes the
/// typed check closed.
#[test]
fn a_frozen_cut_reifies_to_the_command_il()
{
    let pattern = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Pair", [
            ProdPat::ctor("Unit", []),
            ProdPat::ctor("Inl", [ProdPat::ctor("Unit", [])]),
        ]),
        ConsPat::top(),
    );
    let mut arena = CommandArena::new();
    let command =
        reify_command(&mut arena, &pattern, &core_resolver()).expect("a ground cut reifies");
    assert_eq!(
        "⟨pair((), inl(())) |+ ★⟩",
        render_command(&arena, command),
        "node for node"
    );
    assert_eq!(
        NodeCount::from(4_usize),
        arena.producer_count(),
        "four constructors"
    );
    assert_eq!(NodeCount::from(1_usize), arena.command_count(), "one cut");
    assert_eq!(
        Ok(FreeSet::default()),
        check_command(&arena, command),
        "well formed and closed"
    );
}

/// `⟨Unit |+ Inl⁻(★)⟩` reifies to `⟨() |+ μ̃x. ⟨inl(x0) |+ ★⟩⟩`; a frame
/// over a binary constructor is refused. The run suite runs the reified
/// command to the re-wrapped value.
#[test]
fn a_return_frame_reifies_to_a_mu_tilde()
{
    let pattern = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Unit", []),
        ConsPat::frame("Inl", ConsPat::top()),
    );
    let mut arena = CommandArena::new();
    let command =
        reify_command(&mut arena, &pattern, &core_resolver()).expect("a unary frame reifies");
    assert_eq!(
        "⟨() |+ μ̃x. ⟨inl(x0) |+ ★⟩⟩",
        render_command(&arena, command),
        "the frame's definiens"
    );
    assert_eq!(
        Ok(FreeSet::default()),
        check_command(&arena, command),
        "well formed and closed"
    );

    let binary = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Unit", []),
        ConsPat::frame("Pair", ConsPat::top()),
    );
    assert_eq!(
        Err(ReifyRefusal::ArityMismatch {
            constructor: Sym::new("Pair"),
            expected: ProducerArity::TWO,
            found: ProducerArity::ONE,
        }),
        reify_command(&mut arena, &binary, &core_resolver()),
        "a frame re-wraps one value"
    );
}

/// An untyped cell operation frame is refused rather than made an IL
/// request.
#[test]
fn an_operation_frame_is_the_opaque_boundary()
{
    let pattern = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Unit", []),
        ConsPat::op("add", [ProdPat::ctor("Unit", [])], ConsPat::top()),
    );
    let mut arena = CommandArena::new();
    assert_eq!(
        Err(ReifyRefusal::OperationFrame(Sym::new("add"))),
        reify_command(&mut arena, &pattern, &core_resolver()),
        "the opaque boundary"
    );
}

/// A pattern whose producer reifies and whose consumer is refused leaves
/// the arena at its mark; so do an unresolved symbol and a metavariable.
#[test]
fn a_refused_reification_leaves_the_arena_at_its_mark()
{
    let mut arena = CommandArena::new();
    let earlier = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Unit", []),
        ConsPat::top(),
    );
    reify_command(&mut arena, &earlier, &core_resolver()).expect("a ground cut reifies");
    let mark = arena.watermark();

    let open = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Pair", [
            ProdPat::ctor("Unit", []),
            ProdPat::ctor("Unit", []),
        ]),
        ConsPat::meta("k"),
    );
    assert_eq!(
        Err(ReifyRefusal::Metavariable(MetaVar::consumer("k"))),
        reify_command(&mut arena, &open, &core_resolver()),
        "an open consumer is not ground"
    );
    assert_eq!(
        mark,
        arena.watermark(),
        "the producer minted before the refusal is dropped"
    );

    let unknown = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Zero", []),
        ConsPat::top(),
    );
    assert_eq!(
        Err(ReifyRefusal::UnresolvedConstructor(Sym::new("Zero"))),
        reify_command(&mut arena, &unknown, &core_resolver()),
        "a symbol the resolver does not name"
    );
    let framed_open = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Unit", []),
        ConsPat::frame("Inl", ConsPat::meta("k")),
    );
    assert_eq!(
        Err(ReifyRefusal::Metavariable(MetaVar::consumer("k"))),
        reify_command(&mut arena, &framed_open, &core_resolver()),
        "a frame over an open continuation"
    );
    assert_eq!(
        mark,
        arena.watermark(),
        "every refusal leaves the arena at its mark"
    );
}

/// Nested unequal frames and all constructor heads reify closed, and a cut
/// keeps its polarity unchecked. The run suite runs the frames in order.
#[test]
fn reification_preserves_nested_frames_and_constructor_heads()
{
    use gandr_kernel_strata::Level;

    let mut resolver = core_resolver();
    resolver.insert(Sym::new("Lift"), ConstructorTag::Lift(Level::zero()));
    let pattern = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Pair", [
            ProdPat::ctor("Lift", [ProdPat::ctor("Inr", [ProdPat::ctor("Unit", [])])]),
            ProdPat::ctor("Inl", [ProdPat::ctor("Unit", [])]),
        ]),
        ConsPat::frame("Inl", ConsPat::frame("Inr", ConsPat::top())),
    );
    let mut arena = CommandArena::new();
    let command = reify_command(&mut arena, &pattern, &resolver).expect("ground pattern");
    assert_eq!(Ok(FreeSet::default()), check_command(&arena, command));
    let negative = CmdPat::cut(
        Polarity::Negative,
        ProdPat::ctor("Unit", []),
        ConsPat::top(),
    );
    let command = reify_command(&mut arena, &negative, &resolver)
        .expect("reification preserves polarity without checking it");
    assert_eq!("⟨() |− ★⟩", render_command(&arena, command));
}

/// Refusal order is left to right and arity precedes children; existing
/// nodes survive.
#[test]
fn resolution_refusals_preserve_order_and_arena_prefix()
{
    let resolver = core_resolver();
    let mut arena = CommandArena::new();
    let prefix = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Unit", []),
        ConsPat::top(),
    );
    let kept = reify_command(&mut arena, &prefix, &resolver).expect("ground prefix");
    let mark = arena.watermark();
    for (pattern, expected) in [
        (
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Pair", [ProdPat::ctor("Unit", []), ProdPat::meta("hole")]),
                ConsPat::top(),
            ),
            ReifyRefusal::Metavariable(MetaVar::producer("hole")),
        ),
        (
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Pair", [
                    ProdPat::ctor("FirstMissing", []),
                    ProdPat::ctor("LastMissing", []),
                ]),
                ConsPat::top(),
            ),
            ReifyRefusal::UnresolvedConstructor(Sym::new("FirstMissing")),
        ),
        (
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Unit", [ProdPat::meta("too-late")]),
                ConsPat::top(),
            ),
            ReifyRefusal::ArityMismatch {
                constructor: Sym::new("Unit"),
                expected: ProducerArity::ZERO,
                found: ProducerArity::ONE,
            },
        ),
        (
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Pair", []),
                ConsPat::top(),
            ),
            ReifyRefusal::ArityMismatch {
                constructor: Sym::new("Pair"),
                expected: ProducerArity::TWO,
                found: ProducerArity::ZERO,
            },
        ),
        (
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Unit", []),
                ConsPat::frame("Unit", ConsPat::top()),
            ),
            ReifyRefusal::ArityMismatch {
                constructor: Sym::new("Unit"),
                expected: ProducerArity::ZERO,
                found: ProducerArity::ONE,
            },
        ),
        (
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Unit", []),
                ConsPat::frame("MissingFrame", ConsPat::op("later", [], ConsPat::top())),
            ),
            ReifyRefusal::UnresolvedConstructor(Sym::new("MissingFrame")),
        ),
    ] {
        assert_eq!(
            Err(expected),
            reify_command(&mut arena, &pattern, &resolver)
        );
        assert_eq!(mark, arena.watermark());
        assert_eq!("⟨() |+ ★⟩", render_command(&arena, kept));
    }
}
