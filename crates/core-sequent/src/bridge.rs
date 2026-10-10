//! The bridge from cells: a ground command pattern of the cell substrate
//! reified into the command IL.
//!
//! A cell's patterns name constructors by symbol, since the rewriting stack
//! ranges over declared data the IL's [`ConstructorTag`] does not name; a
//! [`ConstructorResolver`] the caller supplies says which symbols are which
//! tags. Over it, [`reify_command`] lowers a ground `⟨p |ε c⟩` node for node:
//! a constructor application to a constructor producer, `★` to `★`, and a
//! return-side frame `K⁻(c)` to its definiens `μ̃x. ⟨K(x) |+ c⟩`. A
//! metavariable, an unresolved symbol, an arity its tag contradicts and an
//! operation frame — the opaque boundary of the host and fusion fragment —
//! are refused by name, and a refused reification leaves the arena at its
//! mark.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsRef;
use gandr_theory_cell_complexes::ConsView;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdRef;
use gandr_theory_cell_complexes::ProdView;
use gandr_theory_cell_complexes::Sym;

use crate::boundary::ProducerArity;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::MintRefusal;
use crate::il::ProducerId;
use crate::il::ProducerNode;

/// Which cell symbols name which of the IL's constructors.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ConstructorResolver
{
    /// Each resolved symbol's tag.
    entries: BTreeMap<Sym, ConstructorTag>,
}

impl ConstructorResolver
{
    /// A resolver naming nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Resolve `symbol` to `tag`, answering the tag it resolved to before.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn insert(
        &mut self,
        symbol: Sym,
        tag: ConstructorTag,
    ) -> Option<ConstructorTag>
    {
        self.entries.insert(symbol, tag)
    }

    /// The tag `symbol` resolves to, or `None`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        symbol: &Sym,
    ) -> Option<&ConstructorTag>
    {
        self.entries.get(symbol)
    }
}

/// Why a command pattern has no reification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReifyRefusal
{
    /// A metavariable: the pattern is not ground.
    Metavariable(MetaVar),
    /// A constructor symbol the resolver does not name.
    UnresolvedConstructor(Sym),
    /// A constructor applied to, or a frame re-wrapping, a number of values
    /// its tag does not declare.
    ArityMismatch
    {
        /// The constructor's symbol.
        constructor: Sym,
        /// The arity its tag declares.
        expected: ProducerArity,
        /// The arity the pattern gives it.
        found: ProducerArity,
    },
    /// An operation frame: the opaque boundary no IL node stands for.
    OperationFrame(Sym),
    /// The arena refused a node.
    Mint(MintRefusal),
    /// An internal invariant broke: a constructor found fewer reified
    /// arguments than it pushed. Unreachable while the walk's own pushes are
    /// the only source of steps; reported rather than asserted.
    ReificationInvariant,
}

impl fmt::Display for ReifyRefusal
{
    /// Names the pattern node with no reification.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Metavariable(ref var) => write!(f, "metavariable {} is not ground", var.hole()),
            | Self::UnresolvedConstructor(ref symbol) => {
                write!(f, "constructor {symbol} names no tag of the IL")
            },
            | Self::ArityMismatch {
                ref constructor,
                expected,
                found,
            } => write!(
                f,
                "constructor {constructor} takes {expected} values, given {found}"
            ),
            | Self::OperationFrame(ref op) => {
                write!(f, "operation frame {op} is the opaque boundary")
            },
            | Self::Mint(refusal) => write!(f, "the command arena refused a node: {refusal}"),
            | Self::ReificationInvariant => f.write_str("the reification lost a node it minted"),
        }
    }
}

impl core::error::Error for ReifyRefusal
{
}

impl From<MintRefusal> for ReifyRefusal
{
    /// Carries the arena's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: MintRefusal) -> Self
    {
        Self::Mint(refusal)
    }
}

/// Reify a ground command pattern into `arena`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the command the pattern denotes, at the pattern's
///   polarity: each constructor application a constructor producer over its
///   reified arguments, `★` the terminal consumer, and each return-side frame
///   `K⁻(c)` the binder `μ̃x. ⟨K(x0) |+ c⟩`.
/// - provides: the cells' entry into the IL the machine runs.
/// - fails: [`ReifyRefusal`] at the first metavariable, unresolved symbol,
///   arity mismatch or operation frame; `arena` is then exactly as on entry.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — finite ground cuts over the core constructor heads have
///   exact structural readings; distinct nested return frames expose reversal
///   and omission. A negative cut retains its polarity without a claim of type
///   correctness. Open patterns, unknown symbols and wrong arities have exact
///   first refusals and preserve a populated arena prefix.
/// - witness: `bridge::tests::a_frozen_cut_reifies_to_the_command_il`
/// - witness: `bridge::tests::a_return_frame_reifies_to_a_mu_tilde`
/// - witness: `bridge::tests::an_operation_frame_is_the_opaque_boundary`
/// - witness: `bridge::tests::a_refused_reification_leaves_the_arena_at_its_mark`
/// - witness: `bridge::tests::reification_preserves_nested_frames_and_constructor_heads`
/// - witness: `bridge::tests::resolution_refusals_preserve_order_and_arena_prefix`
#[inline]
#[spec(
    captures: [entry = arena.watermark()],
    ensures: |ref ret| match ret.as_ref() {
        | Ok(&command) => matches!(arena.command(command), Some(&crate::il::CommandNode::Cut { polarity, .. }) if polarity == pattern.polarity()),
        | Err(_) => arena.watermark() == entry,
    },
)]
pub fn reify_command(
    arena: &mut CommandArena,
    pattern: &CmdPat,
    resolver: &ConstructorResolver,
) -> Result<CommandId, ReifyRefusal>
{
    let mark = arena.watermark();
    let answer = reify(arena, pattern, resolver);
    if answer.is_err() {
        arena.truncate_to(mark);
    }
    answer
}

/// [`reify_command`] without its rollback.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the reified producer and consumer form a cut at the pattern's
///   polarity.
/// - provides: the construction inside the public rollback boundary.
/// - fails: as [`reify_command`], retaining any nodes already minted.
/// - panics: none.
///
/// # Errors
/// As [`reify_command`].
///
/// # Adequacy
/// - hypothesis: L3 — constructor trees and nested return frames have exact
///   core readings, while a negative pattern retains its cut polarity. Refusal
///   after a producer was built is observed at the public rollback boundary;
///   this distinguishes swapped halves and a fixed polarity.
/// - witness: `bridge::tests::a_frozen_cut_reifies_to_the_command_il`
/// - witness: `bridge::tests::reification_preserves_nested_frames_and_constructor_heads`
/// - witness: `bridge::tests::a_refused_reification_leaves_the_arena_at_its_mark`
#[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&command|
    arena.command(command).is_some_and(|&crate::il::CommandNode::Cut { polarity, producer, consumer }|
        polarity == pattern.polarity() && arena.producer(producer).is_some() && arena.consumer(consumer).is_some())))]
fn reify(
    arena: &mut CommandArena,
    pattern: &CmdPat,
    resolver: &ConstructorResolver,
) -> Result<CommandId, ReifyRefusal>
{
    let producer = reify_producer(arena, pattern.producer().to_ref(), resolver)?;
    let consumer = reify_consumer(arena, pattern.consumer().to_ref(), resolver)?;
    Ok(arena.mint_cut(pattern.polarity(), producer, consumer)?)
}

/// The tag a constructor symbol resolves to, held to an arity.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the resolved tag when its declared producer arity is `found`.
/// - provides: the one resolution both halves of a cut make.
/// - fails: [`ReifyRefusal::UnresolvedConstructor`] or
///   [`ReifyRefusal::ArityMismatch`].
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — nullary, unary and binary resolved heads admit their
///   declared arity; too few and too many arguments and an unknown symbol have
///   exact symbol, expected-count and found-count refusals. This distinguishes
///   a fixed arity and a fallback resolution.
/// - witness: `bridge::tests::reification_preserves_nested_frames_and_constructor_heads`
/// - witness: `bridge::tests::a_return_frame_reifies_to_a_mu_tilde`
/// - witness: `bridge::tests::resolution_refusals_preserve_order_and_arena_prefix`
#[spec(ensures: |ref ret| match ret.as_ref() {
    | Ok(tag) => resolver.get(symbol) == Some(tag) && tag.producer_arity() == found,
    | Err(error) => match *error {
        | ReifyRefusal::UnresolvedConstructor(ref missing) => missing == symbol && resolver.get(symbol).is_none(),
        | ReifyRefusal::ArityMismatch { ref constructor, expected, found: observed } => constructor == symbol && observed == found
            && expected != found && resolver.get(symbol).is_some_and(|tag| tag.producer_arity() == expected),
        | _ => false,
    },
})]
fn resolved(
    resolver: &ConstructorResolver,
    symbol: &Sym,
    found: ProducerArity,
) -> Result<ConstructorTag, ReifyRefusal>
{
    let tag = resolver
        .get(symbol)
        .ok_or_else(|| ReifyRefusal::UnresolvedConstructor(symbol.clone()))?;
    let expected = tag.producer_arity();
    if expected == found {
        Ok(tag.clone())
    }
    else {
        Err(ReifyRefusal::ArityMismatch {
            constructor: symbol.clone(),
            expected,
            found,
        })
    }
}

/// One pending unit of producer reification.
enum Step<'pattern>
{
    /// Reify a subtree; leaves one producer.
    Enter(ProdRef<'pattern>),
    /// Pop a constructor's reified arguments and mint it.
    Exit(ConstructorTag, ProducerArity),
}

/// Reify a producer pattern.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the constructor producers the pattern denotes, children minted
///   before their parent.
/// - provides: the producer half of [`reify_command`].
/// - fails: a metavariable, an unresolved symbol, an arity mismatch, or a
///   refused mint.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — nested unit, pair, both injections and lift constructors
///   are observed as exact core nodes after execution. An open producer and two
///   differently invalid fields expose metavariable handling and left-to-right
///   refusal; arity is checked before children.
/// - witness: `bridge::tests::reification_preserves_nested_frames_and_constructor_heads`
/// - witness: `bridge::tests::resolution_refusals_preserve_order_and_arena_prefix`
#[spec(ensures: |ref ret| match root.view() {
    | ProdView::Meta(var) => ret.as_ref().is_err_and(|error| matches!(*error, ReifyRefusal::Metavariable(ref found) if found == var)),
    | ProdView::Ctor { ctor, args } => ret.is_err() || ret.as_ref().is_ok_and(|&id|
        arena.producer(id).is_some_and(|node| matches!(*node, ProducerNode::Constructor { ref tag, ref producers, ref consumers }
            if resolver.get(ctor) == Some(tag) && producers.len() == args.len() && consumers.is_empty()))),
})]
fn reify_producer(
    arena: &mut CommandArena,
    root: ProdRef<'_>,
    resolver: &ConstructorResolver,
) -> Result<ProducerId, ReifyRefusal>
{
    let mut steps = alloc::vec![Step::Enter(root)];
    let mut minted: Vec<ProducerId> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            | Step::Enter(node) => match node.view() {
                | ProdView::Meta(var) => return Err(ReifyRefusal::Metavariable(var.clone())),
                | ProdView::Ctor { ctor, args } => {
                    let arity = ProducerArity::from(args.len());
                    let tag = resolved(resolver, ctor, arity)?;
                    steps.push(Step::Exit(tag, arity));
                    let first_child = steps.len();
                    steps.extend(args.map(Step::Enter));
                    if let Some(children) = steps.get_mut(first_child ..) {
                        children.reverse();
                    }
                },
            },
            | Step::Exit(tag, arity) => {
                let start = minted
                    .len()
                    .checked_sub(usize::from(arity))
                    .ok_or(ReifyRefusal::ReificationInvariant)?;
                let producers: Box<[ProducerId]> = minted.drain(start ..).collect();
                let id = arena.mint_producer(ProducerNode::Constructor {
                    tag,
                    producers,
                    consumers: Box::from([]),
                })?;
                minted.push(id);
            },
        }
    }
    minted.pop().ok_or(ReifyRefusal::ReificationInvariant)
}

/// Reify a consumer pattern.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `★`, wrapped outward by one `μ̃x. ⟨K(x0) |+ ·⟩` per return-side
///   frame, the frame meeting the cut outermost.
/// - provides: the consumer half of [`reify_command`].
/// - fails: a metavariable, an operation frame, an unresolved symbol, a frame
///   over a constructor of arity other than one, or a refused mint.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — top and two differently named nested return frames are
///   observed by the exact wrapped result; open tails, operation frames,
///   unresolved heads and non-unary heads have exact refusals. This
///   distinguishes frame reversal, skipped tails and an incorrect arity rule;
///   the domain is the current constructor vocabulary.
/// - witness: `bridge::tests::a_return_frame_reifies_to_a_mu_tilde`
/// - witness: `bridge::tests::reification_preserves_nested_frames_and_constructor_heads`
/// - witness: `bridge::tests::an_operation_frame_is_the_opaque_boundary`
/// - witness: `bridge::tests::a_refused_reification_leaves_the_arena_at_its_mark`
/// - witness: `bridge::tests::resolution_refusals_preserve_order_and_arena_prefix`
#[spec(ensures: |ref ret| match root.view() {
    | ConsView::Meta(var) => ret.as_ref().is_err_and(|error| matches!(*error, ReifyRefusal::Metavariable(ref found) if found == var)),
    | ConsView::Op { op, .. } => ret.as_ref().is_err_and(|error| matches!(*error, ReifyRefusal::OperationFrame(ref found) if found == op)),
    | ConsView::Top => ret.is_err() || ret.as_ref().is_ok_and(|&id| matches!(arena.consumer(id), Some(&ConsumerNode::Top))),
    | ConsView::Frame { ctor, .. } => ret.is_err() || ret.as_ref().is_ok_and(|&id|
        arena.consumer(id).is_some_and(|node| matches!(*node, ConsumerNode::MuTilde { body }
            if arena.command(body).is_some_and(|&crate::il::CommandNode::Cut { polarity, producer, .. }|
                polarity == Polarity::Positive && arena.producer(producer).is_some_and(|wrapped|
                    matches!(*wrapped, ProducerNode::Constructor { ref tag, ref producers, ref consumers }
                        if resolver.get(ctor) == Some(tag) && producers.len() == 1 && consumers.is_empty()
                            && producers.first().is_some_and(|&bound|
                                matches!(arena.producer(bound), Some(&ProducerNode::Variable { zone: Zone::Intuitionistic, index }) if index == DeBruijnIndex::from(0_u32))))))))),
})]
fn reify_consumer(
    arena: &mut CommandArena,
    root: ConsRef<'_>,
    resolver: &ConstructorResolver,
) -> Result<ConsumerId, ReifyRefusal>
{
    let mut frames: Vec<ConstructorTag> = Vec::new();
    let mut cursor = root;
    loop {
        match cursor.view() {
            | ConsView::Meta(var) => return Err(ReifyRefusal::Metavariable(var.clone())),
            | ConsView::Op { op, .. } => return Err(ReifyRefusal::OperationFrame(op.clone())),
            | ConsView::Top => break,
            | ConsView::Frame { ctor, ret } => {
                frames.push(resolved(resolver, ctor, ProducerArity::ONE)?);
                cursor = ret;
            },
        }
    }
    let mut consumer = arena.mint_consumer(ConsumerNode::Top)?;
    while let Some(tag) = frames.pop() {
        let bound = arena.mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        })?;
        let wrapped = arena.mint_producer(ProducerNode::Constructor {
            tag,
            producers: Box::from([bound]),
            consumers: Box::from([]),
        })?;
        let body = arena.mint_cut(Polarity::Positive, wrapped, consumer)?;
        consumer = arena.mint_consumer(ConsumerNode::MuTilde { body })?;
    }
    Ok(consumer)
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_kernel_term::Side;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::ProdPat;

    use super::*;
    use crate::boundary::NodeCount;
    use crate::boundary::StepCount;
    use crate::check::FreeSet;
    use crate::check::check_command;
    use crate::machine::Definitions;
    use crate::machine::Machine;
    use crate::machine::Outcome;
    use crate::pretty::render_command;

    /// The core's own constructors under the names a test pattern uses.
    ///
    /// # Specification
    /// trivial.
    fn core_resolver() -> ConstructorResolver
    {
        let mut resolver = ConstructorResolver::new();
        resolver.insert(Sym::new("Unit"), ConstructorTag::Unit);
        resolver.insert(Sym::new("Pair"), ConstructorTag::Pair);
        resolver.insert(Sym::new("Inl"), ConstructorTag::Injection(Side::Left));
        resolver.insert(Sym::new("Inr"), ConstructorTag::Injection(Side::Right));
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

    /// `⟨Unit |+ Inl⁻(★)⟩` reifies to `⟨() |+ μ̃x. ⟨inl(x0) |+ ★⟩⟩`, which
    /// runs to the re-wrapped value; a frame over a binary constructor is
    /// refused.
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

        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let Ok(Outcome::Halted(value)) = machine.run(command, StepCount::from(64_usize))
        else {
            panic!("the reified command halts");
        };
        let mut core = CoreArena::new();
        let back = machine
            .read_back(value, &mut core)
            .expect("the value reads back");
        let mut shown = CommandArena::new();
        let mut provenance = crate::focus::Provenance::new();
        let focused = crate::focus::focus_computation(&core, back, &mut shown, &mut provenance)
            .expect("focuses");
        assert_eq!(
            "⟨inl(()) |+ ★⟩",
            render_command(&shown, focused),
            "the frame re-wrapped the value"
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

    /// An operation frame has no IL node: it is refused by name.
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

    /// Nested unequal frames and all constructor heads retain their semantic
    /// order.
    #[test]
    fn reification_preserves_nested_frames_and_constructor_heads()
    {
        use gandr_core_term::Value;
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
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let Ok(Outcome::Halted(value)) = machine.run(command, StepCount::from(64_usize))
        else {
            panic!("reified frames return");
        };
        let mut core = CoreArena::new();
        let read = machine
            .read_back_value(value, &mut core)
            .expect("positive result");
        let Some(&Value::Injection(Side::Right, outer)) = core.value(read)
        else {
            panic!("the last frame wraps last");
        };
        let Some(&Value::Injection(Side::Left, pair)) = core.value(outer)
        else {
            panic!("the first frame wraps first");
        };
        let Some(&Value::Pair(lift, right)) = core.value(pair)
        else {
            panic!("pair head survives");
        };
        let Some(&Value::Lift { ref target, body }) = core.value(lift)
        else {
            panic!("first field is lifted");
        };
        assert_eq!(&Level::zero(), target);
        let Some(&Value::Injection(Side::Right, first_unit)) = core.value(body)
        else {
            panic!("right injection survives under lift");
        };
        let Some(&Value::Injection(Side::Left, last_unit)) = core.value(right)
        else {
            panic!("left injection remains the second field");
        };
        assert_eq!(Some(&Value::Unit), core.value(first_unit));
        assert_eq!(Some(&Value::Unit), core.value(last_unit));
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
}
