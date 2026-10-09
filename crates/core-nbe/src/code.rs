//! Two codes compared as they stand: the types two quotes carry, walked in
//! lockstep through the environments the quotes close over.
//!
//! # A code is compared as a leaf
//!
//! A quote suspends a type over an environment, and a type has no weak head,
//! so the conversion machine has no rule that decomposes two codes into
//! subgoals. It compares them whole instead, in two passes:
//!
//! - **α-equality.** The two types are walked in lockstep. A variable bound by
//!   a dependent arrow or a static lambda inside the type is matched by the
//!   binder it names, a variable free in the quote is read through the quote's
//!   environment, a constant by its position, a static application by its
//!   operator and its argument — whether written in the quote or held as a
//!   neutral's static spine — and a nested code by the same walk over its own
//!   closure. A decode whose code reads as a quote is the quoted type, read at
//!   the quote's place: core-term and the kernel fire that rule when they mint
//!   a decode, and an environment holds codes no mint saw, so the walk fires it
//!   too. Equal walks are [`CodeComparison::Equal`].
//! - **Rigidity.** Two codes that are not α-equal are [`CodeComparison::Apart`]
//!   only when neither holds anything that could still unfold: a constant with
//!   a body, a neutral stuck on an elimination, or a value no code can be. A
//!   static lambda counts as unfolding too: η could still equate it with a
//!   stuck operator, and the walk does not expand it to find out. Anything else
//!   is [`CodeComparison::Undecided`], and the machine declines rather than
//!   answer, which is the honest answer at a rung where nothing reduces inside
//!   a type.
//!
//! The rigidity criterion is the one the kernel's replay applies to a shared
//! comparison, so an answer of [`CodeComparison::Apart`] is one the kernel
//! separates in its own terms.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;

use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::arena::ValueClosureId;
use crate::conv::ConversionFault;
use crate::domain::BinderLevel;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::NeutralHead;
use crate::domain::Unfolding;
use crate::eval::Definitions;

/// What comparing two codes found.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CodeComparison
{
    /// The two types are α-equal.
    Equal,
    /// They are not, and nothing in either could unfold.
    Apart,
    /// They are not α-equal, and something in one could still unfold.
    Undecided,
}

/// How a comparison reads a constant a quoted type names.
#[derive(Clone, Copy, Debug)]
pub enum ConstantReading<'run>
{
    /// Without the definitions: every constant may unfold.
    Unread,
    /// Through the definitions of the run.
    Read(Definitions<'run>),
}

/// Whether something can still unfold.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Rigidity
{
    /// Nothing in it can.
    Rigid,
    /// Something in it can.
    Flexible,
}

/// Whether two walks found their sides alike.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Alike
{
    /// Every pair matched.
    Same,
    /// Some pair did not.
    Different,
}

impl Alike
{
    /// Whether two payloads are equal.
    ///
    /// # Specification
    /// trivial.
    fn between<T>(
        one: &T,
        other: &T,
    ) -> Self
    where
        T: PartialEq,
    {
        if one == other {
            Self::Same
        }
        else {
            Self::Different
        }
    }
}

/// A binder a walk crossed inside quoted types, by a number both sides share.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Binder(u32);

impl Binder
{
    /// The binder numbered after this one.
    ///
    /// # Specification
    /// trivial.
    const fn after(self) -> Self
    {
        Self(self.0.saturating_add(1_u32))
    }
}

/// A chain of binders a walk has crossed inside quoted types, innermost
/// first: each entry names the binder by a number both sides share.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Chain(usize);

/// One link of a [`Chain`]: the binder's shared number and the chain outside
/// it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Link
{
    /// The binder's shared number.
    binder: Binder,
    /// The chain outside it, or the empty chain at link zero.
    outer: Chain,
}

/// Where a node of one side stands: the closure whose environment its free
/// variables read, and the binders crossed since the closure's quote.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Place
{
    /// The quote's closure.
    closure: ValueClosureId,
    /// The binders crossed inside the closure's type.
    chain: Chain,
}

/// How many leading eliminations of a held neutral's spine a node reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SpinePrefix(usize);

/// A node of one side, at its place.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A value type.
    ValueType(ValueTypeId, Place),
    /// A computation type.
    CompType(CompTypeId, Place),
    /// A code inside a decode.
    Code(ValueId, Place),
    /// A domain value an environment holds.
    Held(DomainValueId),
    /// A held neutral read as its head and the first so many of its static
    /// applications.
    Stuck(NeutralId, SpinePrefix),
}

/// What a code reads as, once its variables are resolved.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Atom
{
    /// A binder crossed inside a quoted type, by its shared number.
    Local(Binder),
    /// A variable of the context, by level.
    Variable(Zone, BinderLevel),
    /// A constant, and whether it can unfold.
    Constant(ConstantIndex, Rigidity),
    /// A value-type quote at its place.
    Quote(ValueTypeId, Place),
    /// A computation-type quote at its place.
    QuoteComputation(CompTypeId, Place),
    /// A lift of a code, by the lift node itself, at its place.
    Lift(ValueId, Place),
    /// A static application, by its operator and its argument.
    Applied(Node, Node),
    /// A static lambda, by the lambda node itself, at its place.
    Operator(ValueId, Place),
    /// Anything else, which compares by identity alone.
    Other(Node),
}

/// The comparison's state: the shared binder chains and the binders numbered
/// so far.
struct Walk<'run>
{
    /// The core arena the quotes are written in.
    core: &'run CoreArena,
    /// The domain arena the environments are held in.
    domain: &'run DomainArena,
    /// How a constant is read.
    constants: ConstantReading<'run>,
    /// Every chain link minted, chain `n + 1` being link `n`.
    links: Vec<Link>,
    /// The next binder number.
    next: Binder,
}

impl<'run> Walk<'run>
{
    /// A walk over `core` and `domain`.
    ///
    /// # Specification
    /// trivial.
    fn new(
        core: &'run CoreArena,
        domain: &'run DomainArena,
        constants: ConstantReading<'run>,
    ) -> Self
    {
        Self {
            core,
            domain,
            constants,
            links: Vec::new(),
            next: Binder::default(),
        }
    }

    /// The place a quote's type stands at: its own closure, no binder crossed.
    ///
    /// # Specification
    /// trivial.
    const fn opened(closure: ValueClosureId) -> Place
    {
        Place {
            closure,
            chain: Chain(0_usize),
        }
    }

    /// The places one binder further in on both sides, the binder numbered
    /// alike on each.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two places whose innermost binder carries one fresh shared
    ///   number.
    /// - provides: the step past a dependent arrow's binder in lockstep.
    /// - fails: never.
    /// - panics: none.
    fn crossed(
        &mut self,
        left: Place,
        right: Place,
    ) -> (Place, Place)
    {
        let binder = self.next;
        self.next = binder.after();
        let mut deeper = |place: Place| {
            self.links.push(Link {
                binder,
                outer: place.chain,
            });
            Place {
                closure: place.closure,
                chain: Chain(self.links.len()),
            }
        };
        let left = deeper(left);
        let right = deeper(right);
        (left, right)
    }

    /// The place one binder further in on one side.
    ///
    /// # Specification
    /// trivial.
    fn crossed_alone(
        &mut self,
        place: Place,
    ) -> Place
    {
        let binder = self.next;
        self.next = binder.after();
        self.links.push(Link {
            binder,
            outer: place.chain,
        });
        Place {
            closure: place.closure,
            chain: Chain(self.links.len()),
        }
    }

    /// The binder `index` names inside `chain`, or how far past the chain's
    /// binders it reaches.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the shared number of the binder when `index` counts within
    ///   the chain, and the index less the chain's length otherwise.
    /// - provides: the split between a variable a quoted type binds and one it
    ///   reads from its environment.
    /// - fails: never.
    /// - panics: none.
    fn local(
        &self,
        chain: Chain,
        index: DeBruijnIndex,
    ) -> Result<Binder, DeBruijnIndex>
    {
        let mut remaining = u32::from(index);
        let mut at = chain;
        while let Some(position) = at.0.checked_sub(1_usize) {
            let Some(link) = self.links.get(position)
            else {
                break;
            };
            if remaining == 0_u32 {
                return Ok(link.binder);
            }
            remaining = remaining.saturating_sub(1_u32);
            at = link.outer;
        }
        Err(DeBruijnIndex::from(remaining))
    }

    /// What `node` reads as.
    ///
    /// # Specification
    /// - requires: `node` is a code, a held value or a stuck prefix.
    /// - ensures: the atom the code resolves to: a bound variable as its
    ///   binder, a free one through its closure's environment, a constant with
    ///   its rigidity, a quote, a lift or a static lambda at its place, a
    ///   static application — written, or the last of a held neutral's static
    ///   spine — as its operator and argument, and everything else as itself.
    /// - provides: the one resolution both passes read codes through.
    /// - fails: [`ConversionFault::Domain`] when a closure or a held value does
    ///   not resolve, and [`ConversionFault::MachineInvariant`] when a variable
    ///   reaches past its closure's environment.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    fn atom(
        &self,
        node: Node,
    ) -> Result<Atom, ConversionFault>
    {
        let dangling = ConversionFault::Domain(DomainFault::Dangling);
        let held = match node {
            | Node::Code(code, place) => {
                let written = self
                    .core
                    .value(code)
                    .ok_or(ConversionFault::MachineInvariant)?;
                match *written {
                    | Value::Variable { zone, index } => {
                        let free = match zone {
                            | Zone::Intuitionistic => match self.local(place.chain, index) {
                                | Ok(binder) => return Ok(Atom::Local(binder)),
                                | Err(free) => free,
                            },
                            | Zone::Linear => index,
                        };
                        let closure = self.domain.value_closure(place.closure).ok_or(dangling)?;
                        closure
                            .environment()
                            .lookup(zone, free)
                            .ok_or(ConversionFault::MachineInvariant)?
                    },
                    | Value::Constant(constant) => {
                        return Ok(Atom::Constant(constant, self.constant(constant)));
                    },
                    | Value::Quote(quoted) => return Ok(Atom::Quote(quoted, place)),
                    | Value::QuoteComputation(quoted) => {
                        return Ok(Atom::QuoteComputation(quoted, place));
                    },
                    | Value::Lift { .. } => return Ok(Atom::Lift(code, place)),
                    | Value::StaticLambda(_) => return Ok(Atom::Operator(code, place)),
                    | Value::StaticApplication(head, argument) => {
                        return Ok(Atom::Applied(
                            Node::Code(head, place),
                            Node::Code(argument, place),
                        ));
                    },
                    | Value::Unit
                    | Value::Literal(_)
                    | Value::Pair(..)
                    | Value::Injection(..)
                    | Value::Thunk(_) => return Ok(Atom::Other(node)),
                }
            },
            | Node::Held(value) => value,
            | Node::Stuck(neutral, prefix) => return self.stuck(neutral, prefix),
            | Node::ValueType(..) | Node::CompType(..) => return Ok(Atom::Other(node)),
        };
        let stood = Node::Held(held);
        match *self.domain.value(held).ok_or(dangling)? {
            | DomainValue::Neutral { neutral, .. } => {
                let stuck = self.domain.neutral(neutral).ok_or(dangling)?;
                self.stuck(neutral, SpinePrefix(stuck.spine().len()))
            },
            | DomainValue::Code { code, .. } => {
                let closure = self.domain.value_closure(code).ok_or(dangling)?;
                let place = Self::opened(code);
                match *self
                    .core
                    .value(closure.body())
                    .ok_or(ConversionFault::MachineInvariant)?
                {
                    | Value::Quote(quoted) => Ok(Atom::Quote(quoted, place)),
                    | Value::QuoteComputation(quoted) => Ok(Atom::QuoteComputation(quoted, place)),
                    | Value::Variable { .. }
                    | Value::Constant(_)
                    | Value::Unit
                    | Value::Literal(_)
                    | Value::Pair(..)
                    | Value::Injection(..)
                    | Value::Thunk(_)
                    | Value::Lift { .. }
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..) => Ok(Atom::Other(stood)),
                }
            },
            | DomainValue::StaticLambda { lambda, .. } => {
                let closure = self.domain.value_closure(lambda).ok_or(dangling)?;
                Ok(Atom::Operator(closure.body(), Self::opened(lambda)))
            },
            | DomainValue::Unit { .. }
            | DomainValue::Literal { .. }
            | DomainValue::Pair { .. }
            | DomainValue::Injection { .. }
            | DomainValue::Thunk { .. }
            | DomainValue::Lift { .. } => Ok(Atom::Other(stood)),
        }
    }

    /// What a held neutral reads as, cut to its head and the first `length`
    /// eliminations of its spine.
    ///
    /// # Specification
    /// - requires: `prefix` counts within the neutral's spine.
    /// - ensures: for no elimination, the head — a variable by level, a
    ///   constant with its rigidity, a module form as itself; for a static
    ///   application last, the prefix before it applied to its argument; for
    ///   any other elimination last, the prefix as itself.
    /// - provides: the one reading of a stuck operator spine, so a written
    ///   static application and a held one compare by the same pairwise walk.
    /// - fails: [`ConversionFault::Domain`] when the neutral does not resolve,
    ///   and [`ConversionFault::MachineInvariant`] when `prefix` counts past
    ///   its spine.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by an operator spine compared against a
    ///   written application, a head alone, and spines differing by head and by
    ///   arity.
    /// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
    #[spec(ensures: |ret| match ret {
        | Ok(Atom::Applied(Node::Stuck(cut, SpinePrefix(shorter)), _)) => {
            cut == neutral && shorter < prefix.0
        },
        | Err(ConversionFault::Domain(_)) => self.domain.neutral(neutral).is_none(),
        | Ok(_) | Err(_) => true,
    })]
    fn stuck(
        &self,
        neutral: NeutralId,
        prefix: SpinePrefix,
    ) -> Result<Atom, ConversionFault>
    {
        let held = self
            .domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let Some(last) = prefix.0.checked_sub(1_usize)
        else {
            return Ok(match held.head() {
                | NeutralHead::Variable { zone, level } => Atom::Variable(zone, level),
                | NeutralHead::Constant(constant) => {
                    let rigidity = match held.unfolding() {
                        | Unfolding::Rigid => Rigidity::Rigid,
                        | Unfolding::Unforced(_) | Unfolding::Forced(_) => Rigidity::Flexible,
                    };
                    Atom::Constant(constant, rigidity)
                },
                | NeutralHead::Module(_) => Atom::Other(Node::Stuck(neutral, prefix)),
            });
        };
        match held.spine().get(last) {
            | Some(&Elimination::StaticApply(argument)) => Ok(Atom::Applied(
                Node::Stuck(neutral, SpinePrefix(last)),
                Node::Held(argument),
            )),
            | Some(
                &(Elimination::Apply(_)
                | Elimination::Force
                | Elimination::Bind(_)
                | Elimination::Case { .. }),
            ) => Ok(Atom::Other(Node::Stuck(neutral, prefix))),
            | None => Err(ConversionFault::MachineInvariant),
        }
    }

    /// Whether a constant the core names can unfold here.
    ///
    /// # Specification
    /// trivial.
    fn constant(
        &self,
        constant: ConstantIndex,
    ) -> Rigidity
    {
        match self.constants {
            | ConstantReading::Unread => Rigidity::Flexible,
            | ConstantReading::Read(definitions) => match definitions.unfolding(constant) {
                | Unfolding::Rigid => Rigidity::Rigid,
                | Unfolding::Unforced(_) | Unfolding::Forced(_) => Rigidity::Flexible,
            },
        }
    }

    /// Whether two codes are α-equal.
    ///
    /// # Specification
    /// - requires: both closures hold quotes or static lambdas.
    /// - ensures: [`Alike::Same`] exactly when the lockstep walk finds every
    ///   pair of formers alike, every pair of bound variables naming one
    ///   binder, and every pair of resolved atoms alike.
    /// - provides: the first pass.
    /// - fails: as [`Walk::atom`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Walk::atom`].
    fn equal(
        &mut self,
        left: ValueClosureId,
        right: ValueClosureId,
    ) -> Result<Alike, ConversionFault>
    {
        let mut pending: Vec<(Node, Node)> = Vec::new();
        let left_atom = self.closure_atom(left)?;
        let right_atom = self.closure_atom(right)?;
        let mut atoms = Vec::from([(left_atom, right_atom)]);
        loop {
            while let Some((one, other)) = atoms.pop() {
                match (one, other) {
                    | (Atom::Quote(first, here), Atom::Quote(second, there)) => {
                        pending
                            .push((Node::ValueType(first, here), Node::ValueType(second, there)));
                    },
                    | (
                        Atom::QuoteComputation(first, here),
                        Atom::QuoteComputation(second, there),
                    ) => {
                        pending.push((Node::CompType(first, here), Node::CompType(second, there)));
                    },
                    | (Atom::Lift(first, here), Atom::Lift(second, there)) => {
                        let (
                            Some(&Value::Lift {
                                target: ref left_target,
                                body: left_body,
                            }),
                            Some(&Value::Lift {
                                target: ref right_target,
                                body: right_body,
                            }),
                        ) = (self.core.value(first), self.core.value(second))
                        else {
                            return Err(ConversionFault::MachineInvariant);
                        };
                        if left_target != right_target {
                            return Ok(Alike::Different);
                        }
                        let one = self.atom(Node::Code(left_body, here))?;
                        let other = self.atom(Node::Code(right_body, there))?;
                        atoms.push((one, other));
                    },
                    | (
                        Atom::Applied(head, argument),
                        Atom::Applied(other_head, other_argument),
                    ) => {
                        let arguments = (self.atom(argument)?, self.atom(other_argument)?);
                        let heads = (self.atom(head)?, self.atom(other_head)?);
                        atoms.push(arguments);
                        atoms.push(heads);
                    },
                    | (Atom::Operator(first, here), Atom::Operator(second, there)) => {
                        let (
                            Some(&Value::StaticLambda(left_body)),
                            Some(&Value::StaticLambda(right_body)),
                        ) = (self.core.value(first), self.core.value(second))
                        else {
                            return Err(ConversionFault::MachineInvariant);
                        };
                        let (inside, other_inside) = self.crossed(here, there);
                        let one = self.atom(Node::Code(left_body, inside))?;
                        let other = self.atom(Node::Code(right_body, other_inside))?;
                        atoms.push((one, other));
                    },
                    | (Atom::Local(first), Atom::Local(second)) if first == second => {},
                    | (Atom::Variable(zone, first), Atom::Variable(other_zone, second))
                        if (zone, first) == (other_zone, second) => {},
                    | (Atom::Constant(first, _), Atom::Constant(second, _)) if first == second => {
                    },
                    | (Atom::Other(first), Atom::Other(second)) if first == second => {},
                    | (
                        Atom::Local(_)
                        | Atom::Variable(..)
                        | Atom::Constant(..)
                        | Atom::Quote(..)
                        | Atom::QuoteComputation(..)
                        | Atom::Lift(..)
                        | Atom::Applied(..)
                        | Atom::Operator(..)
                        | Atom::Other(_),
                        _,
                    ) => return Ok(Alike::Different),
                }
            }
            let Some((one, other)) = pending.pop()
            else {
                return Ok(Alike::Same);
            };
            if self.formers(one, other, &mut pending, &mut atoms)? == Alike::Different {
                return Ok(Alike::Different);
            }
        }
    }

    /// The atom a closure's own body reads as.
    ///
    /// # Specification
    /// trivial.
    fn closure_atom(
        &self,
        closure: ValueClosureId,
    ) -> Result<Atom, ConversionFault>
    {
        let held = self
            .domain
            .value_closure(closure)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        self.atom(Node::Code(held.body(), Self::opened(closure)))
    }

    /// The node `node` reads as once every decode of a quote at its root has
    /// fired: `El ⌜A⌝` is `A`, read at the quote's own place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a value-type decode whose code resolves to a value quote is
    ///   replaced by the quoted type, and a computation-type decode whose code
    ///   resolves to a computation quote by the quoted computation type, until
    ///   the root is neither; every other node unchanged.
    /// - provides: the decoding rule core-term and the kernel fire on mint,
    ///   fired here on a code an environment holds, where no mint saw it — so
    ///   an instantiated body, decoded when it was minted, and the closure the
    ///   machine evaluated it as compare alike.
    /// - fails: as [`Walk::atom`]; [`ConversionFault::MachineInvariant`] when a
    ///   type node does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Termination
    /// - reason: the `loop` fires one decode per iteration, not recursion.
    /// - measure: the quotes nested beneath the node, read through the
    ///   environments, which each iteration enters one deeper and which a
    ///   finite domain arena bounds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a value decode and a computation decode
    ///   of a held quote, and a decode beside a type it is not.
    /// - witness: `code::tests::a_decode_of_a_held_quote_compares_as_its_quoted_type`
    #[spec(ensures: |ret| match ret {
        | Ok(Node::ValueType(at, place)) => match self.core.value_type(at) {
            | Some(&ValueType::Element { code, .. }) => {
                !matches!(self.atom(Node::Code(code, place)), Ok(Atom::Quote(..)))
            },
            | _ => true,
        },
        | Ok(Node::CompType(at, place)) => match self.core.comp_type(at) {
            | Some(&CompType::Element { code, .. }) => {
                !matches!(self.atom(Node::Code(code, place)), Ok(Atom::QuoteComputation(..)))
            },
            | _ => true,
        },
        | Ok(_) | Err(_) => true,
    })]
    fn decoded(
        &self,
        node: Node,
    ) -> Result<Node, ConversionFault>
    {
        let mut node = node;
        loop {
            let (code, place) = match node {
                | Node::ValueType(at, place) => match *self
                    .core
                    .value_type(at)
                    .ok_or(ConversionFault::MachineInvariant)?
                {
                    | ValueType::Element { code, .. } => (code, place),
                    | ValueType::Base(_)
                    | ValueType::Unit
                    | ValueType::Product(..)
                    | ValueType::Sum(..)
                    | ValueType::Thunk(_)
                    | ValueType::Universe { .. }
                    | ValueType::Lift { .. }
                    | ValueType::Abstract(_)
                    | ValueType::StaticPi { .. } => return Ok(node),
                },
                | Node::CompType(at, place) => match *self
                    .core
                    .comp_type(at)
                    .ok_or(ConversionFault::MachineInvariant)?
                {
                    | CompType::Element { code, .. } => (code, place),
                    | CompType::Returner(_) | CompType::Arrow { .. } | CompType::Pi { .. } => {
                        return Ok(node);
                    },
                },
                | Node::Code(..) | Node::Held(_) | Node::Stuck(..) => return Ok(node),
            };
            node = match (node, self.atom(Node::Code(code, place))?) {
                | (Node::ValueType(..), Atom::Quote(quoted, there)) => {
                    Node::ValueType(quoted, there)
                },
                | (Node::CompType(..), Atom::QuoteComputation(quoted, there)) => {
                    Node::CompType(quoted, there)
                },
                | _ => return Ok(node),
            };
        }
    }

    /// Compare one pair of type nodes' formers, queueing their children.
    ///
    /// # Specification
    /// - requires: `one` and `other` are type nodes of the same family.
    /// - ensures: [`Alike::Different`] when the formers or their payloads
    ///   differ, read after every decode of a quote at either root has fired,
    ///   and otherwise [`Alike::Same`] with the children queued: type children
    ///   as nodes, a decode's code as an atom pair, a dependent arrow's
    ///   codomain one shared binder further in.
    /// - provides: the per-former step of the first pass.
    /// - fails: [`ConversionFault::MachineInvariant`] when a node does not
    ///   resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// As above, and as [`Walk::atom`].
    fn formers(
        &mut self,
        one: Node,
        other: Node,
        pending: &mut Vec<(Node, Node)>,
        atoms: &mut Vec<(Atom, Atom)>,
    ) -> Result<Alike, ConversionFault>
    {
        let one = self.decoded(one)?;
        let other = self.decoded(other)?;
        match (one, other) {
            | (Node::ValueType(first, here), Node::ValueType(second, there)) => {
                let (Some(left), Some(right)) =
                    (self.core.value_type(first), self.core.value_type(second))
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                match (left, right) {
                    | (&ValueType::Base(a), &ValueType::Base(b)) => Ok(Alike::between(&a, &b)),
                    | (&ValueType::Unit, &ValueType::Unit) => Ok(Alike::Same),
                    | (&ValueType::Abstract(a), &ValueType::Abstract(b)) => {
                        Ok(Alike::between(&a, &b))
                    },
                    | (
                        &ValueType::Universe {
                            ref sort,
                            ref level,
                        },
                        &ValueType::Universe {
                            sort: ref other_sort,
                            level: ref other_level,
                        },
                    ) => Ok(Alike::between(&(sort, level), &(other_sort, other_level))),
                    | (&ValueType::Product(a, b), &ValueType::Product(c, d))
                    | (&ValueType::Sum(a, b), &ValueType::Sum(c, d))
                    | (
                        &ValueType::StaticPi {
                            domain: a,
                            codomain: b,
                        },
                        &ValueType::StaticPi {
                            domain: c,
                            codomain: d,
                        },
                    ) => {
                        pending.push((Node::ValueType(b, here), Node::ValueType(d, there)));
                        pending.push((Node::ValueType(a, here), Node::ValueType(c, there)));
                        Ok(Alike::Same)
                    },
                    | (&ValueType::Thunk(a), &ValueType::Thunk(b)) => {
                        pending.push((Node::CompType(a, here), Node::CompType(b, there)));
                        Ok(Alike::Same)
                    },
                    | (
                        &ValueType::Lift { inner, ref target },
                        &ValueType::Lift {
                            inner: other_inner,
                            target: ref other_target,
                        },
                    ) => {
                        if target != other_target {
                            return Ok(Alike::Different);
                        }
                        pending.push((
                            Node::ValueType(inner, here),
                            Node::ValueType(other_inner, there),
                        ));
                        Ok(Alike::Same)
                    },
                    | (
                        &ValueType::Element { code, ref target },
                        &ValueType::Element {
                            code: other_code,
                            target: ref other_target,
                        },
                    ) => {
                        if target != other_target {
                            return Ok(Alike::Different);
                        }
                        let left_atom = self.atom(Node::Code(code, here))?;
                        let right_atom = self.atom(Node::Code(other_code, there))?;
                        atoms.push((left_atom, right_atom));
                        Ok(Alike::Same)
                    },
                    | (
                        &(ValueType::Base(_)
                        | ValueType::Unit
                        | ValueType::Product(..)
                        | ValueType::Sum(..)
                        | ValueType::Thunk(_)
                        | ValueType::Universe { .. }
                        | ValueType::Lift { .. }
                        | ValueType::Element { .. }
                        | ValueType::Abstract(_)
                        | ValueType::StaticPi { .. }),
                        _,
                    ) => Ok(Alike::Different),
                }
            },
            | (Node::CompType(first, here), Node::CompType(second, there)) => {
                let (Some(left), Some(right)) =
                    (self.core.comp_type(first), self.core.comp_type(second))
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                match (left, right) {
                    | (&CompType::Returner(a), &CompType::Returner(b)) => {
                        pending.push((Node::ValueType(a, here), Node::ValueType(b, there)));
                        Ok(Alike::Same)
                    },
                    | (
                        &CompType::Arrow { domain, codomain },
                        &CompType::Arrow {
                            domain: other_domain,
                            codomain: other_codomain,
                        },
                    ) => {
                        pending.push((
                            Node::CompType(codomain, here),
                            Node::CompType(other_codomain, there),
                        ));
                        pending.push((
                            Node::ValueType(domain, here),
                            Node::ValueType(other_domain, there),
                        ));
                        Ok(Alike::Same)
                    },
                    | (
                        &CompType::Pi { domain, codomain },
                        &CompType::Pi {
                            domain: other_domain,
                            codomain: other_codomain,
                        },
                    ) => {
                        let (inside, other_inside) = self.crossed(here, there);
                        pending.push((
                            Node::CompType(codomain, inside),
                            Node::CompType(other_codomain, other_inside),
                        ));
                        pending.push((
                            Node::ValueType(domain, here),
                            Node::ValueType(other_domain, there),
                        ));
                        Ok(Alike::Same)
                    },
                    | (
                        &CompType::Element { code, ref target },
                        &CompType::Element {
                            code: other_code,
                            target: ref other_target,
                        },
                    ) => {
                        if target != other_target {
                            return Ok(Alike::Different);
                        }
                        let left_atom = self.atom(Node::Code(code, here))?;
                        let right_atom = self.atom(Node::Code(other_code, there))?;
                        atoms.push((left_atom, right_atom));
                        Ok(Alike::Same)
                    },
                    | (
                        &(CompType::Returner(_)
                        | CompType::Arrow { .. }
                        | CompType::Pi { .. }
                        | CompType::Element { .. }),
                        _,
                    ) => Ok(Alike::Different),
                }
            },
            | (
                Node::ValueType(..)
                | Node::CompType(..)
                | Node::Code(..)
                | Node::Held(_)
                | Node::Stuck(..),
                _,
            ) => Ok(Alike::Different),
        }
    }

    /// Whether anything in a code can still unfold.
    ///
    /// # Specification
    /// - requires: `closure` holds a quote or a static lambda.
    /// - ensures: [`Rigidity::Rigid`] exactly when every atom the quoted type
    ///   reaches — through its decodes, nested quotes, static applications and
    ///   environment — is a bound or free variable, a constant without a body,
    ///   or a quote whose own type is rigid; a static lambda anywhere is
    ///   [`Rigidity::Flexible`], η being able to equate it with a stuck
    ///   operator.
    /// - provides: the second pass.
    /// - fails: as [`Walk::atom`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Walk::atom`].
    fn rigidity(
        &mut self,
        closure: ValueClosureId,
    ) -> Result<Rigidity, ConversionFault>
    {
        let mut atoms = Vec::from([self.closure_atom(closure)?]);
        let mut types: Vec<Node> = Vec::new();
        while !atoms.is_empty() || !types.is_empty() {
            while let Some(atom) = atoms.pop() {
                match atom {
                    | Atom::Local(_) | Atom::Variable(..) | Atom::Constant(_, Rigidity::Rigid) => {
                    },
                    | Atom::Constant(_, Rigidity::Flexible)
                    | Atom::Operator(..)
                    | Atom::Other(_) => {
                        return Ok(Rigidity::Flexible);
                    },
                    | Atom::Applied(head, argument) => {
                        atoms.push(self.atom(argument)?);
                        atoms.push(self.atom(head)?);
                    },
                    | Atom::Quote(quoted, place) => types.push(Node::ValueType(quoted, place)),
                    | Atom::QuoteComputation(quoted, place) => {
                        types.push(Node::CompType(quoted, place));
                    },
                    | Atom::Lift(lift, place) => {
                        let Some(&Value::Lift { body, .. }) = self.core.value(lift)
                        else {
                            return Err(ConversionFault::MachineInvariant);
                        };
                        atoms.push(self.atom(Node::Code(body, place))?);
                    },
                }
            }
            let Some(node) = types.pop()
            else {
                break;
            };
            match node {
                | Node::ValueType(id, place) => {
                    match *self
                        .core
                        .value_type(id)
                        .ok_or(ConversionFault::MachineInvariant)?
                    {
                        | ValueType::Base(_)
                        | ValueType::Unit
                        | ValueType::Universe { .. }
                        | ValueType::Abstract(_) => {},
                        | ValueType::Product(first, second)
                        | ValueType::Sum(first, second)
                        | ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        } => {
                            types.push(Node::ValueType(first, place));
                            types.push(Node::ValueType(second, place));
                        },
                        | ValueType::Thunk(body) => types.push(Node::CompType(body, place)),
                        | ValueType::Lift { inner, .. } => {
                            types.push(Node::ValueType(inner, place));
                        },
                        | ValueType::Element { code, .. } => {
                            atoms.push(self.atom(Node::Code(code, place))?);
                        },
                    }
                },
                | Node::CompType(id, place) => {
                    match *self
                        .core
                        .comp_type(id)
                        .ok_or(ConversionFault::MachineInvariant)?
                    {
                        | CompType::Returner(result) => types.push(Node::ValueType(result, place)),
                        | CompType::Arrow { domain, codomain } => {
                            types.push(Node::ValueType(domain, place));
                            types.push(Node::CompType(codomain, place));
                        },
                        | CompType::Pi { domain, codomain } => {
                            types.push(Node::ValueType(domain, place));
                            let inside = self.crossed_alone(place);
                            types.push(Node::CompType(codomain, inside));
                        },
                        | CompType::Element { code, .. } => {
                            atoms.push(self.atom(Node::Code(code, place))?);
                        },
                    }
                },
                | Node::Code(..) | Node::Held(_) | Node::Stuck(..) => {
                    return Err(ConversionFault::MachineInvariant);
                },
            }
        }
        Ok(Rigidity::Rigid)
    }
}

/// Compare two codes or two type operators, each closed over its
/// environment.
///
/// # Specification
/// - requires: `left` and `right` are value closures of `domain` whose bodies
///   are quotes or static lambdas written in `core`.
/// - ensures: [`CodeComparison::Equal`] when the two are α-equal read through
///   their environments, a decode of a quote read as the quoted type;
///   [`CodeComparison::Apart`] when they are not and neither holds anything
///   that could unfold; and [`CodeComparison::Undecided`] otherwise — always so
///   for two operators that are not α-equal.
/// - provides: the one comparison of two codes or two operators, which
///   conversion's structural step and the machine's rule table both read.
/// - fails: [`ConversionFault::Domain`] for a closure or a held value that does
///   not resolve, and [`ConversionFault::MachineInvariant`] for a core node
///   that does not.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the three answers, separated by two quotes of one type,
///   two of different rigid types, and two of different types one of which
///   decodes a defined constant; with the environment read through by two
///   quotes over one variable, and a decode of a held quote read as the quoted
///   type in both families; and the static formers by a written application
///   against a held static spine, two heads and two arguments apart, and two
///   operators alike and unlike.
/// - witness: `code::tests::two_quotes_of_one_type_are_equal`
/// - witness: `code::tests::rigid_quotes_of_different_types_are_apart`
/// - witness: `code::tests::a_quote_over_a_defined_constant_is_undecided`
/// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
/// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
/// - witness: `code::tests::a_decode_of_a_held_quote_compares_as_its_quoted_type`
pub fn compare_codes(
    core: &CoreArena,
    domain: &DomainArena,
    constants: ConstantReading<'_>,
    left: ValueClosureId,
    right: ValueClosureId,
) -> Result<CodeComparison, ConversionFault>
{
    let mut walk = Walk::new(core, domain, constants);
    if walk.equal(left, right)? == Alike::Same {
        return Ok(CodeComparison::Equal);
    }
    match (walk.rigidity(left)?, walk.rigidity(right)?) {
        | (Rigidity::Rigid, Rigidity::Rigid) => Ok(CodeComparison::Apart),
        | (Rigidity::Rigid | Rigidity::Flexible, _) => Ok(CodeComparison::Undecided),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;

    use super::CodeComparison;
    use super::ConstantReading;
    use super::compare_codes;
    use crate::arena::DomainArena;
    use crate::arena::DomainValueId;
    use crate::arena::ValueClosureId;
    use crate::closure::Environment;
    use crate::domain::BinderLevel;
    use crate::domain::DomainValue;
    use crate::domain::Elimination;
    use crate::domain::NeutralHead;
    use crate::domain::TermFace;
    use crate::domain::Unfolding;
    use crate::eval::Definitions;
    use crate::eval::Fuel;
    use crate::eval::LoweredChain;
    use crate::eval::eval_value_within;

    /// Evaluate the quote `quote` in an environment binding `bound`, outermost
    /// first, and name the code's closure.
    ///
    /// # Specification
    /// - requires: `quote` is a quote whose free variables `bound` binds.
    /// - ensures: the closure the evaluated code suspends.
    /// - panics: when the evaluation refuses or produces no code.
    fn code_of(
        core: &CoreArena,
        domain: &mut DomainArena,
        quote: ValueId,
        bound: &[DomainValueId],
    ) -> ValueClosureId
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut supplied = Environment::new();
        for &value in bound {
            supplied.extend(Zone::Intuitionistic, value);
        }
        let (produced, _) = eval_value_within(
            core,
            domain,
            definitions,
            Fuel::from(64_u32),
            quote,
            supplied,
        )
        .expect("the quote evaluates");
        let Some(&DomainValue::Code { code, .. }) = domain.value(produced)
        else {
            panic!("a quote evaluates to a code");
        };
        code
    }

    /// A rigid variable neutral at `level`, as an environment holds one.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        domain: &mut DomainArena,
        level: BinderLevel,
    ) -> DomainValueId
    {
        let neutral = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level,
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a neutral with no spine mints");
        domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("the neutral resolves")
    }

    /// Compare two codes with no definitions at all, every constant rigid.
    ///
    /// # Specification
    /// trivial.
    fn compare_rigidly(
        core: &CoreArena,
        domain: &DomainArena,
        left: ValueClosureId,
        right: ValueClosureId,
    ) -> CodeComparison
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        compare_codes(
            core,
            domain,
            ConstantReading::Read(definitions),
            left,
            right,
        )
        .expect("both closures hold quotes")
    }

    /// `Thunk(Π(_ : Unit). El(#0, level))` written afresh.
    ///
    /// # Specification
    /// trivial.
    fn dependent_quote(
        core: &mut CoreArena,
        level: Level,
    ) -> ValueId
    {
        let domain = core.value_type_unit();
        let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = core.comp_type_element(bound, level);
        let pi = core.comp_type_pi(domain, decoded);
        let thunk = core.value_type_thunk(pi);
        core.value_quote(thunk)
    }

    #[test]
    fn two_quotes_of_one_type_are_equal()
    {
        let mut core = CoreArena::new();
        let first = dependent_quote(&mut core, Level::zero());
        let second = dependent_quote(&mut core, Level::zero());
        assert_ne!(first, second, "two nodes, so identity cannot answer");

        let mut domain = DomainArena::new();
        let left = code_of(&core, &mut domain, first, &[]);
        let right = code_of(&core, &mut domain, second, &[]);
        assert_eq!(
            CodeComparison::Equal,
            compare_codes(&core, &domain, ConstantReading::Unread, left, right)
                .expect("both closures hold quotes"),
            "the bound variable names one binder on each side, so the walk matches"
        );

        let third = dependent_quote(&mut core, Level::zero().succ().expect("level one exists"));
        let other = code_of(&core, &mut domain, third, &[]);
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, left, other),
            "a decode at another level is another type, and nothing in either unfolds"
        );
    }

    #[test]
    fn rigid_quotes_of_different_types_are_apart()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let unit_quote = core.value_quote(unit);
        let integer = core.value_type_base(BaseType::Integer);
        let integer_quote = core.value_quote(integer);
        let unit_result = core.value_type_unit();
        let returner = core.comp_type_returner(unit_result);
        let computation_quote = core.value_quote_computation(returner);

        let mut domain = DomainArena::new();
        let left = code_of(&core, &mut domain, unit_quote, &[]);
        let right = code_of(&core, &mut domain, integer_quote, &[]);
        let computation = code_of(&core, &mut domain, computation_quote, &[]);
        assert_eq!(
            CodeComparison::Apart,
            compare_codes(&core, &domain, ConstantReading::Unread, left, right)
                .expect("both closures hold quotes"),
            "two closed formers that differ hold nothing that could unfold"
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_codes(&core, &domain, ConstantReading::Unread, left, computation)
                .expect("both closures hold quotes"),
            "and a value-type quote is apart from a computation-type quote"
        );
    }

    #[test]
    fn a_decode_of_a_held_quote_compares_as_its_quoted_type()
    {
        // `El x * El x` over `x := ⌜Integer⌝` against `Integer * Integer`, and
        // `El x` over `x := ⌜F Integer⌝` against `F Integer`: the decoding
        // rule a mint fires, fired where the environment holds the quote.
        let mut core = CoreArena::new();
        let integer = core.value_type_base(BaseType::Integer);
        let integer_quote = core.value_quote(integer);
        let returns = core.comp_type_returner(integer);
        let action_quote = core.value_quote_computation(returns);
        let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = core.value_type_element(bound, Level::zero());
        let squared = core.value_type_product(decoded, decoded);
        let squared_quote = core.value_quote(squared);
        let written = core.value_type_product(integer, integer);
        let written_quote = core.value_quote(written);
        let acting = core.comp_type_element(bound, Level::zero());
        let acting_quote = core.value_quote_computation(acting);
        let string = core.value_type_base(BaseType::String);
        let other = core.value_type_product(integer, string);
        let other_quote = core.value_quote(other);

        let mut domain = DomainArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let held = |domain: &mut DomainArena, quote: ValueId| {
            eval_value_within(
                &core,
                domain,
                definitions,
                Fuel::from(64_u32),
                quote,
                Environment::new(),
            )
            .expect("the quote evaluates")
            .0
        };
        let held_integer = held(&mut domain, integer_quote);
        let held_action = held(&mut domain, action_quote);
        let squared_code = code_of(&core, &mut domain, squared_quote, &[held_integer]);
        let written_code = code_of(&core, &mut domain, written_quote, &[]);
        let other_code = code_of(&core, &mut domain, other_quote, &[]);
        let acting_code = code_of(&core, &mut domain, acting_quote, &[held_action]);
        let action_code = code_of(&core, &mut domain, action_quote, &[]);
        assert_eq!(
            compare_rigidly(&core, &domain, squared_code, written_code),
            CodeComparison::Equal,
            "a value decode of a held quote reads as the quoted type"
        );
        assert_eq!(
            compare_rigidly(&core, &domain, acting_code, action_code),
            CodeComparison::Equal,
            "and so does a computation decode of a held computation quote"
        );
        assert_eq!(
            compare_rigidly(&core, &domain, squared_code, other_code),
            CodeComparison::Apart,
            "a decoded side still differs from a type it is not"
        );
    }

    #[test]
    fn a_quote_over_a_defined_constant_is_undecided()
    {
        let mut core = CoreArena::new();
        let constant = core.value_constant(ConstantIndex::from(0_usize));
        let decoded = core.value_type_element(constant, Level::zero());
        let decode_quote = core.value_quote(decoded);
        let unit = core.value_type_unit();
        let unit_quote = core.value_quote(unit);

        let mut domain = DomainArena::new();
        let left = code_of(&core, &mut domain, decode_quote, &[]);
        let right = code_of(&core, &mut domain, unit_quote, &[]);
        assert_eq!(
            CodeComparison::Undecided,
            compare_codes(&core, &domain, ConstantReading::Unread, left, right)
                .expect("both closures hold quotes"),
            "read without the definitions, the constant may unfold to the unit's quote"
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, left, right),
            "read through definitions that give it no body, it cannot"
        );
    }

    #[test]
    fn a_quoted_variable_is_read_through_the_environment()
    {
        let mut core = CoreArena::new();
        let innermost = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let near = core.value_type_element(innermost, Level::zero());
        let near_quote = core.value_quote(near);
        let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let far = core.value_type_element(outer, Level::zero());
        let far_quote = core.value_quote(far);

        let mut domain = DomainArena::new();
        let x = variable(&mut domain, BinderLevel::from(0_u32));
        let y = variable(&mut domain, BinderLevel::from(1_u32));
        let reads_x_near = code_of(&core, &mut domain, near_quote, &[x]);
        let reads_x_far = code_of(&core, &mut domain, far_quote, &[x, y]);
        let reads_y_near = code_of(&core, &mut domain, near_quote, &[y]);
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, reads_x_near, reads_x_far),
            "two different indices that the two environments resolve to one variable are equal"
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, reads_x_near, reads_y_near),
            "and one index that the environments resolve to two variables is apart"
        );
    }

    #[test]
    fn static_operators_compare_by_binder_and_spine()
    {
        let mut core = CoreArena::new();
        let family = ConstantIndex::from(0_usize);
        let other_family = ConstantIndex::from(1_usize);
        // `⌜El (F #0)⌝` and `⌜El (G #0)⌝`, with the application written in the
        // quote, and `⌜El #0⌝`, whose code an environment supplies.
        let innermost = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let head = core.value_constant(family);
        let other_head = core.value_constant(other_family);
        let written = core.value_static_application(head, innermost);
        let other_written = core.value_static_application(other_head, innermost);
        let written_decode = core.value_type_element(written, Level::zero());
        let other_decode = core.value_type_element(other_written, Level::zero());
        let plain_decode = core.value_type_element(innermost, Level::zero());
        let written_quote = core.value_quote(written_decode);
        let other_quote = core.value_quote(other_decode);
        let plain_quote = core.value_quote(plain_decode);

        let mut domain = DomainArena::new();
        let x = variable(&mut domain, BinderLevel::from(0_u32));
        let y = variable(&mut domain, BinderLevel::from(1_u32));
        let held_neutral = domain
            .neutral_node(
                NeutralHead::Constant(family),
                Vec::from([Elimination::StaticApply(x)]),
                Unfolding::Rigid,
            )
            .expect("a statically applied neutral mints");
        let held = domain
            .value_neutral(held_neutral, TermFace::Reduced)
            .expect("a static spine stands as a value");

        let written_at_x = code_of(&core, &mut domain, written_quote, &[x]);
        let written_at_y = code_of(&core, &mut domain, written_quote, &[y]);
        let other_at_x = code_of(&core, &mut domain, other_quote, &[x]);
        let held_at_x = code_of(&core, &mut domain, plain_quote, &[held]);
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, written_at_x, held_at_x),
            "a written application and a held static spine compare by head and argument alike"
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, written_at_x, written_at_y),
            "one rigid head at two rigid arguments is apart"
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, written_at_x, other_at_x),
            "two rigid heads at one argument are apart"
        );

        // `λX. ⌜El X⌝` written twice, and `λX. ⌜Unit⌝`.
        let operators = [plain_quote, plain_quote, {
            let unit = core.value_type_unit();
            core.value_quote(unit)
        }]
        .map(|body| core.value_static_lambda(body));
        let [first, second, constant_operator] = operators.map(|lambda| {
            let chain = LoweredChain::new();
            let environment = DefinitionalEnvironment::new();
            let definitions = Definitions::new(&chain, &environment, environment.root());
            let (produced, _) = eval_value_within(
                &core,
                &mut domain,
                definitions,
                Fuel::from(64_u32),
                lambda,
                Environment::new(),
            )
            .expect("a static lambda evaluates");
            let Some(&DomainValue::StaticLambda {
                lambda: closure, ..
            }) = domain.value(produced)
            else {
                panic!("a static lambda evaluates to an operator");
            };
            closure
        });
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, first, second),
            "two operators alike under one shared binder are equal"
        );
        assert_eq!(
            CodeComparison::Undecided,
            compare_rigidly(&core, &domain, first, constant_operator),
            "two operators that differ are undecided: an operator is never declared apart"
        );
    }
}
