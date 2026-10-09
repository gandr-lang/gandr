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
/// - hypothesis: L3 — a ground cut over every constructor head reifies to its
///   exact rendering and passes the typed check closed, a return frame reifies
///   to its `μ̃` definiens and runs to the re-wrapped value, and each refusal
///   leaves the arena at its mark after nodes were minted.
/// - witness: `bridge::tests::a_frozen_cut_reifies_to_the_command_il`
/// - witness: `bridge::tests::a_return_frame_reifies_to_a_mu_tilde`
/// - witness: `bridge::tests::an_operation_frame_is_the_opaque_boundary`
/// - witness: `bridge::tests::a_refused_reification_leaves_the_arena_at_its_mark`
#[inline]
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
/// trivial.
///
/// # Errors
/// As [`reify_command`].
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
}
