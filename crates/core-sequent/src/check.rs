//! The typed-IL check: the well-formedness every command the machine runs is
//! held to.
//!
//! [`check_command`] walks a command and every node below it and refuses, by
//! name:
//!
//! - **reference integrity** — an address the arena does not hold;
//! - **arity** — a constructor or destructor whose producer or consumer
//!   children contradict the counts its head declares, and a match or copattern
//!   object answering one head twice;
//! - **focus** — a `μ` standing as a constructor field or a frame argument,
//!   where only a value may stand;
//! - **polarity** — a cut whose producer or consumer observes the other
//!   polarity: constructors, literals, thunks, matches and force frames are
//!   positive; copattern objects and application frames are negative;
//!   variables, constants, `μ`, covariables, `μ̃` and `★` take the cut's
//!   polarity.
//!
//! On success it answers the command's free variables and covariables, as
//! indices counted from the command itself, so scope is checked by the caller
//! asking for a closed command. The walk is a loop over an explicit stack.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::ConsumerArity;
use crate::boundary::ProducerArity;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::ProducerId;
use crate::il::ProducerNode;

/// A head whose arity a node is held to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ArityHead
{
    /// A constructor head.
    Constructor(ConstructorTag),
    /// A destructor head.
    Destructor(DestructorTag),
}

/// Why a command is not well formed.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CheckRefusal
{
    /// A command address the arena does not hold.
    DanglingCommand(CommandId),
    /// A producer address the arena does not hold.
    DanglingProducer(ProducerId),
    /// A consumer address the arena does not hold.
    DanglingConsumer(ConsumerId),
    /// A `μ` standing where only a value may.
    NonValueArgument(ProducerId),
    /// A cut whose side observes the other polarity.
    PolarityMismatch
    {
        /// The cut.
        command: CommandId,
        /// The cut's polarity.
        cut: Polarity,
        /// The polarity a side observes.
        observed: Polarity,
    },
    /// Producer children contradicting the head's declaration.
    ProducerArity
    {
        /// The head.
        head: ArityHead,
        /// The declared count.
        expected: ProducerArity,
        /// The count found.
        found: ProducerArity,
    },
    /// Consumer children contradicting the head's declaration.
    ConsumerArity
    {
        /// The head.
        head: ArityHead,
        /// The declared count.
        expected: ConsumerArity,
        /// The count found.
        found: ConsumerArity,
    },
    /// A match or copattern object answering one head twice.
    DuplicateArm(ArityHead),
}

impl fmt::Display for CheckRefusal
{
    /// Names the ill-formed node and the rule it breaks.
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
            | Self::DanglingCommand(id) => write!(f, "command {id} is not in the arena"),
            | Self::DanglingProducer(id) => write!(f, "producer {id} is not in the arena"),
            | Self::DanglingConsumer(id) => write!(f, "consumer {id} is not in the arena"),
            | Self::NonValueArgument(id) => {
                write!(f, "producer {id} is a capture where a value must stand")
            },
            | Self::PolarityMismatch { command, .. } => {
                write!(f, "command {command} cuts a side of the other polarity")
            },
            | Self::ProducerArity {
                expected, found, ..
            } => {
                write!(
                    f,
                    "a head declaring {expected} producer children has {found}"
                )
            },
            | Self::ConsumerArity {
                expected, found, ..
            } => {
                write!(
                    f,
                    "a head declaring {expected} consumer children has {found}"
                )
            },
            | Self::DuplicateArm(_) => f.write_str("a head is answered by two arms"),
        }
    }
}

impl core::error::Error for CheckRefusal
{
}

/// The free variables and covariables of a well-formed command, counted from
/// the command itself.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FreeSet
{
    /// The free producer variables, by zone and index.
    producers: BTreeSet<(Zone, DeBruijnIndex)>,
    /// The free covariables.
    covariables: BTreeSet<CovariableIndex>,
}

impl FreeSet
{
    /// The free producer variables, by zone and index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn producers(&self) -> &BTreeSet<(Zone, DeBruijnIndex)>
    {
        &self.producers
    }

    /// The free covariables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn covariables(&self) -> &BTreeSet<CovariableIndex>
    {
        &self.covariables
    }
}

/// Check a command and everything below it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the command's free producer variables and covariables,
///   each index counted from the command; the command is then reference-intact,
///   arity-correct, focused and polarity-consistent.
/// - provides: the one well-formedness judgement over the IL.
/// - fails: the first [`CheckRefusal`] a depth-first walk meets.
/// - panics: none.
/// - intension: one stack entry per node occurrence below the command.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each refusal is reached by a minimal command that breaks
///   only its rule and asserted by exact variant and payload; the arity rule is
///   separated from a constant by one count admitted at one head and refused at
///   the other; scope by one variable free and the same variable bound.
/// - witness: `check::tests::terminal_cut_is_wellformed`
/// - witness: `check::tests::scope_tracks_binders`
/// - witness: `check::tests::dangling_reference_is_rejected`
/// - witness: `check::tests::non_value_argument_is_rejected`
/// - witness: `check::tests::polarity_mismatch_is_rejected`
/// - witness: `check::tests::constructor_arity_is_checked`
/// - witness: `check::tests::constructor_consumer_arity_is_checked`
/// - witness: `check::tests::destructor_consumer_arity_is_checked`
/// - witness: `check::tests::consumer_arity_follows_the_head_not_a_constant`
/// - witness: `check::tests::a_head_answered_twice_is_rejected`
/// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
#[inline]
pub fn check_command(
    arena: &CommandArena,
    command: CommandId,
) -> Result<FreeSet, CheckRefusal>
{
    let mut walk = Walk {
        arena,
        stack: alloc::vec![Visit::Command(command, Depth::default())],
        free: FreeSet::default(),
    };
    while let Some(visit) = walk.stack.pop() {
        match visit {
            | Visit::Command(id, depth) => walk.command(id, depth)?,
            | Visit::Producer(id, depth) => walk.producer(id, depth)?,
            | Visit::Consumer(id, depth) => walk.consumer(id, depth)?,
        }
    }
    Ok(walk.free)
}

/// The binders opened above a node.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Depth
{
    /// Producer binders.
    producers: u32,
    /// Covariable binders.
    covariables: u32,
}

impl Depth
{
    /// The depth under further binders, saturating at a ceiling no arena of at
    /// most `u32::MAX` nodes per family can reach.
    ///
    /// # Specification
    /// trivial.
    fn under(
        self,
        producers: ProducerArity,
        covariables: ConsumerArity,
    ) -> Self
    {
        let widen = |count: usize| u32::try_from(count).unwrap_or(u32::MAX);
        Self {
            producers: self.producers.saturating_add(widen(usize::from(producers))),
            covariables: self
                .covariables
                .saturating_add(widen(usize::from(covariables))),
        }
    }
}

/// One pending node of the walk.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// A command at a depth.
    Command(CommandId, Depth),
    /// A producer at a depth.
    Producer(ProducerId, Depth),
    /// A consumer at a depth.
    Consumer(ConsumerId, Depth),
}

/// The state of one check.
struct Walk<'run>
{
    /// The arena checked.
    arena: &'run CommandArena,
    /// The pending nodes, the next one last.
    stack: Vec<Visit>,
    /// The free set gathered so far.
    free: FreeSet,
}

impl Walk<'_>
{
    /// Check one cut's polarity and schedule its two sides.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the producer and consumer are scheduled at the cut's depth.
    /// - provides: the polarity rule.
    /// - fails: a dangling side, or a side observing the other polarity.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn command(
        &mut self,
        id: CommandId,
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let &CommandNode::Cut {
            polarity,
            producer,
            consumer,
        } = self
            .arena
            .command(id)
            .ok_or(CheckRefusal::DanglingCommand(id))?;
        let sent = self
            .arena
            .producer(producer)
            .ok_or(CheckRefusal::DanglingProducer(producer))?;
        let received = self
            .arena
            .consumer(consumer)
            .ok_or(CheckRefusal::DanglingConsumer(consumer))?;
        for observed in [producer_polarity(sent), consumer_polarity(received)]
            .into_iter()
            .flatten()
        {
            if observed != polarity {
                return Err(CheckRefusal::PolarityMismatch {
                    command: id,
                    cut: polarity,
                    observed,
                });
            }
        }
        self.stack.push(Visit::Consumer(consumer, depth));
        self.stack.push(Visit::Producer(producer, depth));
        Ok(())
    }

    /// Check one producer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a free variable is recorded; children are scheduled under the
    ///   binders their parent opens.
    /// - provides: the arity, focus and scope rules for producers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, or a
    ///   `μ` field.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn producer(
        &mut self,
        id: ProducerId,
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let node = self
            .arena
            .producer(id)
            .ok_or(CheckRefusal::DanglingProducer(id))?;
        match *node {
            | ProducerNode::Variable { zone, index } => {
                let past = match zone {
                    | Zone::Intuitionistic => u32::from(index).checked_sub(depth.producers),
                    | Zone::Linear => Some(u32::from(index)),
                };
                if let Some(past) = past {
                    self.free
                        .producers
                        .insert((zone, DeBruijnIndex::from(past)));
                }
            },
            | ProducerNode::Constant(_) | ProducerNode::Literal(_) => {},
            | ProducerNode::Constructor {
                ref tag,
                ref producers,
                ref consumers,
            } => {
                let head = ArityHead::Constructor(tag.clone());
                self.children(
                    head,
                    tag.producer_arity(),
                    tag.consumer_arity(),
                    producers,
                    consumers,
                    depth,
                )?;
            },
            | ProducerNode::Thunk { body } | ProducerNode::Mu { body } => {
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                ));
            },
            | ProducerNode::Cocase { ref arms } => {
                let mut seen = BTreeSet::new();
                for arm in arms {
                    if !seen.insert(arm.destructor) {
                        return Err(CheckRefusal::DuplicateArm(ArityHead::Destructor(
                            arm.destructor,
                        )));
                    }
                    let under = depth.under(
                        arm.destructor.producer_arity(),
                        arm.destructor.consumer_arity(),
                    );
                    self.stack.push(Visit::Command(arm.body, under));
                }
            },
        }
        Ok(())
    }

    /// Check one consumer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a free covariable is recorded; children are scheduled under
    ///   the binders their parent opens.
    /// - provides: the arity, focus and scope rules for consumers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, or a
    ///   `μ` argument.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn consumer(
        &mut self,
        id: ConsumerId,
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let node = self
            .arena
            .consumer(id)
            .ok_or(CheckRefusal::DanglingConsumer(id))?;
        match *node {
            | ConsumerNode::Covariable(index) => {
                if let Some(past) = u32::from(index).checked_sub(depth.covariables) {
                    self.free.covariables.insert(CovariableIndex::from(past));
                }
            },
            | ConsumerNode::Top => {},
            | ConsumerNode::MuTilde { body } => {
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ONE, ConsumerArity::ZERO),
                ));
            },
            | ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                let head = ArityHead::Destructor(tag);
                self.children(
                    head,
                    tag.producer_arity(),
                    tag.consumer_arity(),
                    producers,
                    consumers,
                    depth,
                )?;
            },
            | ConsumerNode::Case { ref arms } => {
                let mut seen: Vec<&ConstructorTag> = Vec::new();
                for arm in arms {
                    if seen.contains(&&arm.constructor) {
                        return Err(CheckRefusal::DuplicateArm(ArityHead::Constructor(
                            arm.constructor.clone(),
                        )));
                    }
                    seen.push(&arm.constructor);
                    let under = depth.under(
                        arm.constructor.producer_arity(),
                        arm.constructor.consumer_arity(),
                    );
                    self.stack.push(Visit::Command(arm.body, under));
                }
            },
        }
        Ok(())
    }

    /// Hold a constructor's or destructor's children to its head's
    /// declaration and schedule them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the children are scheduled at `depth`.
    /// - provides: the shared arity and focus rule of both kinds of head.
    /// - fails: [`CheckRefusal::ProducerArity`] before
    ///   [`CheckRefusal::ConsumerArity`], then
    ///   [`CheckRefusal::NonValueArgument`] for the first `μ` child, or a
    ///   dangling child.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn children(
        &mut self,
        head: ArityHead,
        producer_arity: ProducerArity,
        consumer_arity: ConsumerArity,
        producers: &[ProducerId],
        consumers: &[ConsumerId],
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let found = ProducerArity::from(producers.len());
        if found != producer_arity {
            return Err(CheckRefusal::ProducerArity {
                head,
                expected: producer_arity,
                found,
            });
        }
        let found = ConsumerArity::from(consumers.len());
        if found != consumer_arity {
            return Err(CheckRefusal::ConsumerArity {
                head,
                expected: consumer_arity,
                found,
            });
        }
        for &producer in producers {
            let node = self
                .arena
                .producer(producer)
                .ok_or(CheckRefusal::DanglingProducer(producer))?;
            if let ProducerNode::Mu { .. } = *node {
                return Err(CheckRefusal::NonValueArgument(producer));
            }
        }
        for &consumer in consumers.iter().rev() {
            self.stack.push(Visit::Consumer(consumer, depth));
        }
        for &producer in producers.iter().rev() {
            self.stack.push(Visit::Producer(producer, depth));
        }
        Ok(())
    }
}

/// The polarity a producer observes, or `None` when it takes the cut's.
///
/// # Specification
/// - ensures: positive for literals, constructors and thunks; negative for
///   copattern objects; `None` for variables, constants and `μ`.
fn producer_polarity(node: &ProducerNode) -> Option<Polarity>
{
    match *node {
        | ProducerNode::Literal(_)
        | ProducerNode::Constructor { .. }
        | ProducerNode::Thunk { .. } => Some(Polarity::Positive),
        | ProducerNode::Cocase { .. } => Some(Polarity::Negative),
        | ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Mu { .. } => {
            None
        },
    }
}

/// The polarity a consumer observes, or `None` when it takes the cut's.
///
/// # Specification
/// - ensures: positive for matches, the polarity its head observes for a
///   destructor frame, `None` for covariables, `μ̃` and `★`.
fn consumer_polarity(node: &ConsumerNode) -> Option<Polarity>
{
    match *node {
        | ConsumerNode::Case { .. } => Some(Polarity::Positive),
        | ConsumerNode::Destructor { tag, .. } => Some(tag.polarity()),
        | ConsumerNode::Covariable(_) | ConsumerNode::MuTilde { .. } | ConsumerNode::Top => None,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;

    use gandr_kernel_term::Side;

    use super::*;
    use crate::il::CopatternArm;
    use crate::il::PatternArm;

    /// Mint the unit producer.
    ///
    /// # Specification
    /// trivial.
    fn unit(arena: &mut CommandArena) -> ProducerId
    {
        arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("a leaf mints")
    }

    /// Mint `★`.
    ///
    /// # Specification
    /// trivial.
    fn top(arena: &mut CommandArena) -> ConsumerId
    {
        arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints")
    }

    /// Build `⟨() |+ consumer⟩`, so a consumer under test is reached in its
    /// ordinary position.
    ///
    /// # Specification
    /// trivial.
    fn cut_against_unit(
        arena: &mut CommandArena,
        consumer: ConsumerNode,
    ) -> CommandId
    {
        let producer = unit(arena);
        let consumer = arena.mint_consumer(consumer).expect("children resolve");
        arena
            .mint_cut(Polarity::Positive, producer, consumer)
            .expect("children resolve")
    }

    /// Build `⟨producer |+ ★⟩`.
    ///
    /// # Specification
    /// trivial.
    fn cut_against_top(
        arena: &mut CommandArena,
        producer: ProducerNode,
    ) -> CommandId
    {
        let producer = arena.mint_producer(producer).expect("children resolve");
        let consumer = top(arena);
        arena
            .mint_cut(Polarity::Positive, producer, consumer)
            .expect("children resolve")
    }

    /// `⟨() |+ ★⟩` is well formed and closed.
    #[test]
    fn terminal_cut_is_wellformed()
    {
        let mut arena = CommandArena::new();
        let root = cut_against_top(&mut arena, ProducerNode::Constructor {
            tag: ConstructorTag::Unit,
            producers: Box::from([]),
            consumers: Box::from([]),
        });
        assert_eq!(
            Ok(FreeSet::default()),
            check_command(&arena, root),
            "the terminal cut has no free variable or covariable"
        );
    }

    /// A variable past every binder is free, counted from the command; the
    /// same index under a `μ̃` is bound. A covariable past a `μ` is free.
    #[test]
    fn scope_tracks_binders()
    {
        let mut arena = CommandArena::new();
        let variable = ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        };
        let root = cut_against_top(&mut arena, variable.clone());
        let free = check_command(&arena, root).expect("well formed");
        assert!(
            free.producers()
                .contains(&(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))),
            "x0 is free at the root"
        );

        let occurrence = arena.mint_producer(variable).expect("a leaf mints");
        let inner_top = top(&mut arena);
        let inner = arena
            .mint_cut(Polarity::Positive, occurrence, inner_top)
            .expect("children resolve");
        let root = cut_against_unit(&mut arena, ConsumerNode::MuTilde { body: inner });
        assert_eq!(
            Ok(FreeSet::default()),
            check_command(&arena, root),
            "the μ̃ binds x0"
        );

        let escaping = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(1_u32)))
            .expect("a leaf mints");
        let value = unit(&mut arena);
        let body = arena
            .mint_cut(Polarity::Positive, value, escaping)
            .expect("children resolve");
        let root = cut_against_top(&mut arena, ProducerNode::Mu { body });
        let free = check_command(&arena, root).expect("well formed");
        assert_eq!(
            Some(&CovariableIndex::from(0_u32)),
            free.covariables().first(),
            "α1 under one μ is the root's free α0"
        );
    }

    /// A root the arena does not hold is dangling.
    #[test]
    fn dangling_reference_is_rejected()
    {
        let arena = CommandArena::new();
        let phantom = CommandId::from(7_u32);
        assert_eq!(
            Err(CheckRefusal::DanglingCommand(phantom)),
            check_command(&arena, phantom),
            "an unresolved command is dangling"
        );
    }

    /// A `μ` as a pair's field is a non-value.
    #[test]
    fn non_value_argument_is_rejected()
    {
        let mut arena = CommandArena::new();
        let value = unit(&mut arena);
        let inner_top = top(&mut arena);
        let inner = arena
            .mint_cut(Polarity::Positive, value, inner_top)
            .expect("children resolve");
        let capture = arena
            .mint_producer(ProducerNode::Mu { body: inner })
            .expect("the body resolves");
        let other = unit(&mut arena);
        let root = cut_against_top(&mut arena, ProducerNode::Constructor {
            tag: ConstructorTag::Pair,
            producers: Box::from([capture, other]),
            consumers: Box::from([]),
        });
        assert_eq!(
            Err(CheckRefusal::NonValueArgument(capture)),
            check_command(&arena, root),
            "a capture in field position is a non-value"
        );
    }

    /// A copattern object cut positively is a polarity mismatch.
    #[test]
    fn polarity_mismatch_is_rejected()
    {
        let mut arena = CommandArena::new();
        let root = cut_against_top(&mut arena, ProducerNode::Cocase {
            arms: Box::from([]),
        });
        let refused = check_command(&arena, root);
        assert!(
            matches!(
                refused,
                Err(CheckRefusal::PolarityMismatch {
                    cut: Polarity::Positive,
                    observed: Polarity::Negative,
                    ..
                })
            ),
            "a copattern object cut positively is refused: {refused:?}"
        );
    }

    /// A pair of one field contradicts its head.
    #[test]
    fn constructor_arity_is_checked()
    {
        let mut arena = CommandArena::new();
        let only = unit(&mut arena);
        let root = cut_against_top(&mut arena, ProducerNode::Constructor {
            tag: ConstructorTag::Pair,
            producers: Box::from([only]),
            consumers: Box::from([]),
        });
        assert_eq!(
            Err(CheckRefusal::ProducerArity {
                head: ArityHead::Constructor(ConstructorTag::Pair),
                expected: ProducerArity::TWO,
                found: ProducerArity::ONE,
            }),
            check_command(&arena, root),
            "a pair needs two fields"
        );
    }

    /// A constructor is held to the consumer arity its head declares, none.
    #[test]
    fn constructor_consumer_arity_is_checked()
    {
        let mut arena = CommandArena::new();
        let stray = top(&mut arena);
        let root = cut_against_top(&mut arena, ProducerNode::Constructor {
            tag: ConstructorTag::Unit,
            producers: Box::from([]),
            consumers: Box::from([stray]),
        });
        assert_eq!(
            Err(CheckRefusal::ConsumerArity {
                head: ArityHead::Constructor(ConstructorTag::Unit),
                expected: ConsumerArity::ZERO,
                found: ConsumerArity::ONE,
            }),
            check_command(&arena, root),
            "no constructor of the core's types carries a consumer"
        );
    }

    /// A destructor frame is held to its one return continuation in both
    /// directions.
    #[test]
    fn destructor_consumer_arity_is_checked()
    {
        let mut arena = CommandArena::new();
        let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([]),
        });
        assert_eq!(
            Err(CheckRefusal::ConsumerArity {
                head: ArityHead::Destructor(DestructorTag::Force),
                expected: ConsumerArity::ONE,
                found: ConsumerArity::ZERO,
            }),
            check_command(&arena, root),
            "a frame without its continuation is refused"
        );
        let first = top(&mut arena);
        let second = top(&mut arena);
        let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([first, second]),
        });
        assert_eq!(
            Err(CheckRefusal::ConsumerArity {
                head: ArityHead::Destructor(DestructorTag::Force),
                expected: ConsumerArity::ONE,
                found: ConsumerArity::from(2_usize),
            }),
            check_command(&arena, root),
            "a frame with two continuations is refused"
        );
    }

    /// The count comes from the head: one consumer child is admitted at a
    /// frame and refused at a constructor, none admitted at a constructor and
    /// refused at a frame.
    #[test]
    fn consumer_arity_follows_the_head_not_a_constant()
    {
        let mut arena = CommandArena::new();
        let one = top(&mut arena);
        let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([one]),
        });
        assert!(
            check_command(&arena, root).is_ok(),
            "one consumer child meets the frame's declaration"
        );
        let root = cut_against_top(&mut arena, ProducerNode::Constructor {
            tag: ConstructorTag::Unit,
            producers: Box::from([]),
            consumers: Box::from([]),
        });
        assert!(
            check_command(&arena, root).is_ok(),
            "no consumer child meets the constructor's declaration"
        );
        let root = cut_against_top(&mut arena, ProducerNode::Constructor {
            tag: ConstructorTag::Unit,
            producers: Box::from([]),
            consumers: Box::from([one]),
        });
        assert!(
            matches!(
                check_command(&arena, root),
                Err(CheckRefusal::ConsumerArity { .. })
            ),
            "the same one child violates the constructor's declaration"
        );
        let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([]),
        });
        assert!(
            matches!(
                check_command(&arena, root),
                Err(CheckRefusal::ConsumerArity { .. })
            ),
            "the same empty list violates the frame's declaration"
        );
    }

    /// A match answering one constructor twice, and a copattern object
    /// answering one destructor twice, are refused by the repeated head.
    #[test]
    fn a_head_answered_twice_is_rejected()
    {
        let mut arena = CommandArena::new();
        let value = unit(&mut arena);
        let inner_top = top(&mut arena);
        let body = arena
            .mint_cut(Polarity::Positive, value, inner_top)
            .expect("children resolve");
        let left = ConstructorTag::Injection(Side::Left);
        let root = cut_against_unit(&mut arena, ConsumerNode::Case {
            arms: Box::from([
                PatternArm {
                    constructor: left.clone(),
                    body,
                },
                PatternArm {
                    constructor: left.clone(),
                    body,
                },
            ]),
        });
        assert_eq!(
            Err(CheckRefusal::DuplicateArm(ArityHead::Constructor(left))),
            check_command(&arena, root),
            "a match answers each constructor once"
        );
        let object = arena
            .mint_producer(ProducerNode::Cocase {
                arms: Box::from([
                    CopatternArm {
                        destructor: DestructorTag::Apply,
                        body,
                    },
                    CopatternArm {
                        destructor: DestructorTag::Apply,
                        body,
                    },
                ]),
            })
            .expect("the arms resolve");
        let outer_top = top(&mut arena);
        let root = arena
            .mint_cut(Polarity::Negative, object, outer_top)
            .expect("children resolve");
        assert_eq!(
            Err(CheckRefusal::DuplicateArm(ArityHead::Destructor(
                DestructorTag::Apply
            ))),
            check_command(&arena, root),
            "an object answers each destructor once"
        );
    }
}
