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
//!
//! # Codes
//!
//! A quote `⌜A⌝` carries a type, and a type has no weak head: nothing in it
//! reduces until something reads it. Evaluation therefore suspends the whole
//! quote over the environment its codes read, as `DomainValue::Code` over a
//! value closure, flexible because the closure is. Readback rebuilds the quoted
//! type former by former: a leaf holding no code is spliced as it stands, a
//! decode's code is evaluated in the quote's environment and read back, and a
//! dependent arrow opens a fresh variable for its codomain the way a lambda's
//! body is opened. Under `ReadbackMode::Unfolding` a code constant therefore
//! unfolds, and a decode of the quote it unfolds to is decoded on mint, so a
//! code reads back in normal form.
//!
//! Conversion compares two codes whole, in two passes. α-equality walks both
//! types in lockstep, matching a bound variable by the binder it names and
//! reading a free one through its quote's environment. Rigidity separates two
//! α-distinct codes only when neither holds a constant with a body, a stuck
//! elimination, or a value no code reads as. The search-free steps read every
//! constant as one that could unfold, and defer; the machine reads the
//! definitions, closes an equal or a rigidly apart pair as one
//! `ComparedShared`, and declines anything else with
//! `DeclineReason::UndecidedCodes`. The kernel's replay closes a shared
//! comparison as equal when the sides are α-equal and separates it only when
//! both are rigid, so an answer here is one the kernel re-derives on its own
//! terms.
//!
//! The lockstep walk gives paired binders one identity and retains each side’s
//! outer chain separately. Its binder counter uses the arena’s index width: a
//! fixed 32-bit counter could alias different binders while a wider link vector
//! still grew. The vector’s size bound precedes the counter’s ceiling.
//! `code::tests::binder_numbers_stay_distinct_across_the_u32_boundary`
//! witnesses distinct inner binders and the preserved outer binder across that
//! boundary.
//!
//! Alternatives: a domain of types with weak-head formers, compared by the rule
//! table, which is type-level reduction this language does not have and a
//! second domain the replay would need a reading of; and codes compared by
//! identity alone, which refutes two quotes of one type written twice.
//! Reversal: a type former that reduces, such as a large elimination, needs
//! types evaluated; codes then become weak heads the rule table decomposes, and
//! the decline goes.
//!
//! The walk fires the decoding rule `gandr-core-term` and the kernel fire on
//! mint, `El ⌜A⌝` is `A`, at a decode whose code resolves to a quote through an
//! environment, where no mint saw it. An operator's body entered at a quoted
//! argument reads such a decode, and the same body minted instantiated holds
//! the quoted type itself, decoded when it was minted; with the rule, the
//! closure the machine evaluated and the reduct the checker minted compare
//! alike, which is the comparison a certificate for one static step makes.
//! Alternatives: leaving the decode in place, which separates every static
//! redex from its instantiated reduct, so no static step certifies; and
//! decoding at evaluation, which gives types a weak head for this one rule.
//! Reversal: as for codes, a type former that reduces, at which point the
//! decode is one step of the rule table.
//!
//! The duplication walk refuses a quote graft by name,
//! `DuplicationFault::Quote`: no producer shares inside a type, so the overlay
//! carries quotes for erasure alone. Reversal: a producer that shares across a
//! type, which makes the type families ribs of the walk.
//!
//! # Static operators
//!
//! A static lambda evaluates to `DomainValue::StaticLambda`, a value closure
//! over the lambda node itself, flexible because the closure is. A static
//! application evaluates its head and its argument, then fires static beta when
//! the head is a static lambda: it extends the closure's environment by the
//! argument and enters the body. Over a neutral it grows the spine by
//! `Elimination::StaticApply`; over anything else it refuses with
//! `EvalFault::AppliedNonOperator`. A family applied to its arguments is
//! therefore one neutral whose spine records them, and the cached word folds
//! the spine in order, so `F(A)` and `F(A, B)` and `G(A)` separate by head
//! index and arity before any comparison runs.
//!
//! Readback under `ReadbackMode::Unfolding` reads back static normal form. A
//! static lambda opens a fresh variable for its body, as a lambda does. A
//! neutral whose head unfolds to an operator has its leading static
//! applications re-applied to the forced body, and the fold resumes after them.
//! No static redex survives readback in that mode. `ReadbackMode::ZeroUnfold`
//! keeps the term face, redexes included, because it is the mode that hands
//! back what the source wrote.
//!
//! Static normalization is confluent: the evaluator's environment machine,
//! normal-order substitution and applicative-order substitution reach one
//! normal form on every simply kinded term the property generates. Static beta
//! is the β of the simply typed λ-calculus over codes, so it is strongly
//! normalizing and confluent, and the machine's fuel only bounds a definition
//! that unfolds into itself.
//!
//! Conversion compares two static lambdas through the code walk, matching their
//! binders by level. A static lambda against a neutral defers in the
//! search-free steps and declines with `DeclineReason::UndecidedCodes` in the
//! machine. The machine never η-expands an operator, and the code walk never
//! declares an operator rigidly apart, because η could relate it to a stuck
//! operator the rigidity reading cannot see through.
//!
//! Alternatives:
//!
//! - static beta in the arena's constructors, which reduces before the
//!   definitions are known and hides the unfolding the checker certifies;
//! - a separate normalizer for codes, which duplicates the environment machine
//!   and its fuel;
//! - η for operators, which needs a static-Pi-typed comparison the untyped
//!   machine does not have.
//!
//! Reversal: a measured family where the decline at a lambda against a neutral
//! costs a refusal a typed η would have answered. Conversion then becomes typed
//! at static Pis.

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
struct Binder(usize);

impl Binder
{
    /// The binder numbered after this one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next arena-width number, saturating only at that width's
    ///   ceiling. A live walk appends at least one link per increment, so its
    ///   vector's size bound is reached before that ceiling.
    /// - provides: distinct binder identities beyond the 32-bit index range.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — successive crossings at the 32-bit ceiling still name
    ///   distinct binders, while the outer binder remains reachable at index
    ///   one; narrowing or saturating the counter at that ceiling aliases them.
    /// - witness: `code::tests::binder_numbers_stay_distinct_across_the_u32_boundary`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(1_usize))]
    const fn after(self) -> Self
    {
        Self(self.0.saturating_add(1_usize))
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
    /// A structural ordinary value used as a nominal argument.
    FirstOrder(Node),
    /// Anything else, which compares by identity alone.
    Other(Node),
}

/// Variable-arity argument children borrowed from syntax or the domain table.
#[derive(Debug)]
enum ArgumentFields<'run>
{
    /// Unevaluated ordered constructor fields.
    Source(core::slice::Iter<'run, ValueId>, Place),
    /// Unevaluated record fields, in label order.
    Record(
        alloc::collections::btree_map::Values<'run, gandr_core_term::FieldLabel, ValueId>,
        Place,
    ),
    /// Evaluated fields, in the same order as their source signature.
    Held(core::slice::Iter<'run, DomainValueId>),
}

impl Iterator for ArgumentFields<'_>
{
    type Item = Node;
    /// Map the next child into its captured reading.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<Node>
    {
        match *self {
            | Self::Source(ref mut values, ref place) => {
                values.next().map(|value| Node::Code(*value, *place))
            },
            | Self::Record(ref mut values, ref place) => {
                values.next().map(|value| Node::Code(*value, *place))
            },
            | Self::Held(ref mut values) => values.next().copied().map(Node::Held),
        }
    }
    /// Preserve the exact remaining child count.
    ///
    /// # Specification
    /// trivial.
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let count = match *self {
            | Self::Source(ref values, _) => values.len(),
            | Self::Record(ref values, _) => values.len(),
            | Self::Held(ref values) => values.len(),
        };
        (count, Some(count))
    }
}

impl ExactSizeIterator for ArgumentFields<'_>
{
}

/// An ordinary structural value as seen through either kind of capture.
#[derive(Debug)]
enum FirstOrder<'run>
{
    /// The empty native list.
    ListNil,
    /// A native list cell, retaining both ordered children.
    ListCons(Node, Node),
    /// An exact literal payload in the core arena.
    Literal(ValueId),
    /// An ordered tuple of any arity, the unit among them.
    Tuple(ArgumentFields<'run>),
    /// A tagged sum value.
    Injection(gandr_kernel_term::Summand, Node),
    /// A constructor with its complete nominal classifier.
    Constructor
    {
        /// The complete nominal classifier, in its captured reading.
        datatype: Node,
        /// The constructor ordinal within that nominal declaration.
        tag: gandr_core_term::ConstructorTag,
        /// Payload values in declaration order.
        fields: ArgumentFields<'run>,
    },
    /// A record with its exact labels and captured field values.
    Record
    {
        /// Source labels, preserving the exact structural record shape.
        labels: &'run alloc::collections::BTreeMap<gandr_core_term::FieldLabel, ValueId>,
        /// Captured values in the same label order.
        fields: ArgumentFields<'run>,
    },
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — paired crossings resolve index zero to one shared
    ///   binder, the next crossing is distinct, and index one still reads the
    ///   outer chain. Reusing a number or linking either side to the wrong
    ///   parent changes alpha comparison.
    /// - witness: `code::tests::binder_numbers_stay_distinct_across_the_u32_boundary`
    /// - witness: `code::tests::local_binders_shadow_only_their_own_chain`
    /// - witness: `code::tests::two_quotes_of_one_type_are_equal`
    /// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
    #[spec(
        captures: [entry_length = self.links.len(), entry_next = self.next],
        ensures: |ret| self.links.len().checked_sub(2) == Some(entry_length)
            && self.next == entry_next.after()
            && ret.0.closure == left.closure && ret.1.closure == right.closure
            && ret.0.chain.0.checked_sub(1) == Some(entry_length)
            && ret.1.chain.0 == self.links.len()
            && self.links.get(entry_length).is_some_and(|link| link.binder == entry_next && link.outer == left.chain)
            && self.links.last().is_some_and(|link| link.binder == entry_next && link.outer == right.chain),
    )]
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
    /// - requires: nothing.
    /// - ensures: one new link carrying the next binder number, with the
    ///   previous chain as its outer link and the same closure at its place.
    /// - provides: the binder extension used by the rigidity walk.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the one-sided crossing preserves the old binder at
    ///   index one while index zero names the new binder, including past the
    ///   32-bit ceiling; losing the outer link or reusing a number changes
    ///   lookup.
    /// - witness: `code::tests::binder_numbers_stay_distinct_across_the_u32_boundary`
    /// - witness: `code::tests::local_binders_shadow_only_their_own_chain`
    #[spec(
        captures: [entry_length = self.links.len(), entry_next = self.next],
        ensures: |ret| self.links.len().checked_sub(1) == Some(entry_length)
            && self.next == entry_next.after() && ret.closure == place.closure
            && ret.chain.0 == self.links.len()
            && self.links.last().is_some_and(|link| link.binder == entry_next && link.outer == place.chain),
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — unequal-length paired chains share their newest
    ///   binder without conflating either older binder, and an index past the
    ///   chain is lowered by exactly its length; a flat-vector offset or
    ///   one-too-many lowering changes the resolved binder or residual index.
    /// - witness: `code::tests::local_binders_shadow_only_their_own_chain`
    /// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
    #[spec(ensures: |ret| {
        let links = core::iter::successors(
            chain.0.checked_sub(1).and_then(|position| self.links.get(position)),
            |link| self.links.get(link.outer.0.checked_sub(1)?));
        match links.clone().enumerate().find(|&(depth, _)| u32::try_from(depth).ok() == Some(u32::from(index))) {
            Some((_, link)) => ret == Ok(link.binder),
            None => ret == Err(DeBruijnIndex::from(u32::from(index).saturating_sub(u32::try_from(links.count()).unwrap_or(u32::MAX)))),
        }
    })]
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
    /// # Adequacy
    /// - hypothesis: L3 — an intuitionistic local shadows only its own chain, a
    ///   linear occurrence still reads its environment, and missing core,
    ///   closure and environment entries have distinct refusals. Written and
    ///   held applications compare alike; resolving through the wrong zone,
    ///   chain or spine changes the atom or comparison.
    /// - witness: `code::tests::local_binders_shadow_only_their_own_chain`
    /// - witness: `code::tests::atom_resolution_refuses_missing_sources_and_preserves_zone`
    /// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
    /// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
    ///
    /// # Errors
    /// As above.
    #[spec(ensures: |ret| {
        let node = match node {
            Node::Code(code, place) => match self.core.value(code) {
                Some(&Value::Variable { zone, index }) => {
                    let free = match zone {
                        Zone::Intuitionistic => match self.local(place.chain, index) {
                            Ok(binder) => return ret == Ok(Atom::Local(binder)),
                            Err(free) => free,
                        },
                        Zone::Linear => index,
                    };
                    let Some(closure) = self.domain.value_closure(place.closure) else {
                        return ret == Err(ConversionFault::Domain(DomainFault::Dangling));
                    };
                    let Some(held) = closure.environment().lookup(zone, free) else {
                        return ret == Err(ConversionFault::MachineInvariant);
                    };
                    Node::Held(held)
                },
                _ => node,
            },
            _ => node,
        };
        match node {
        Node::Code(code, place) => self.core.value(code).map_or_else(|| ret == Err(ConversionFault::MachineInvariant), |matched_native_node| match *matched_native_node {
Value::Constant(constant) => ret == Ok(Atom::Constant(constant, self.constant(constant))),
Value::Quote(quoted) => ret == Ok(Atom::Quote(quoted, place)),
Value::QuoteComputation(quoted) => ret == Ok(Atom::QuoteComputation(quoted, place)),
Value::Lift { .. } => ret == Ok(Atom::Lift(code, place)),
Value::StaticLambda(_) => ret == Ok(Atom::Operator(code, place)),
Value::StaticApplication(head, argument) => ret == Ok(Atom::Applied(Node::Code(head, place), Node::Code(argument, place))),
Value::Constructor { .. } | Value::Record(_) | Value::Tuple(_) | Value::ListNil | Value::ListCons(..) | Value::Literal(_) | Value::Injection(..) => ret == Ok(Atom::FirstOrder(node)),
_ => ret == Ok(Atom::Other(node)),
}),
        Node::Held(value) => self.domain.value(value).map_or_else(|| ret == Err(ConversionFault::Domain(DomainFault::Dangling)), |matched_native_node| match *matched_native_node {
DomainValue::Neutral { neutral, .. } => self.domain.neutral(neutral).map_or_else(
                || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
                |held| ret == self.stuck(neutral, SpinePrefix(held.spine().len()))),
DomainValue::Code { code, .. } => self.domain.value_closure(code).map_or_else(
                || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
                |closure| match closure.body() {
                    crate::ValueBody::ValueType(quoted) => ret == Ok(Atom::Quote(quoted,Self::opened(code))),
                    crate::ValueBody::CompType(quoted) => ret == Ok(Atom::QuoteComputation(quoted,Self::opened(code))),
                    crate::ValueBody::Source(body) => match self.core.value(body) {
                        None => ret == Err(ConversionFault::MachineInvariant),
                        Some(&Value::Quote(quoted)) => ret == Ok(Atom::Quote(quoted,Self::opened(code))),
                        Some(&Value::QuoteComputation(quoted)) => ret == Ok(Atom::QuoteComputation(quoted,Self::opened(code))),
                        Some(_) => ret == Ok(Atom::Other(node)),
                    },
                }),
DomainValue::StaticLambda { lambda, .. } => self.domain.value_closure(lambda).map_or_else(
                || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
                |closure| match closure.body() { crate::ValueBody::Source(body) => ret == Ok(Atom::Operator(body,Self::opened(lambda))), _ => ret == Err(ConversionFault::MachineInvariant) }),
DomainValue::Constructor { .. } | DomainValue::Record { .. } | DomainValue::Tuple { .. } | DomainValue::ListNil { .. } | DomainValue::ListCons { .. } | DomainValue::Literal { .. } | DomainValue::Injection { .. } => ret == Ok(Atom::FirstOrder(node)),
_ => ret == Ok(Atom::Other(node)),
}),
        Node::Stuck(neutral, prefix) => ret == self.stuck(neutral, prefix),
        Node::ValueType(..) | Node::CompType(..) => ret == Ok(Atom::Other(node)),
    } })]
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
                    | Value::Constructor { .. }
                    | Value::Record(_)
                    | Value::Tuple(_)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Literal(_)
                    | Value::Injection(..) => return Ok(Atom::FirstOrder(node)),
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
                    | Value::PathRefl(_)
                    | Value::Here(_)
                    | Value::Stay(_)
                    | Value::Then(..)
                    | Value::FlowProduct(..)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::SessionRelated { .. }
                    | Value::Recorded(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Ua { .. }
                    | Value::Returned(_)
                    | Value::Nested(_)
                    | Value::Run(_)
                    | Value::Reify(_)
                    | Value::Primitive { .. }
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Thunk(_)
                    | Value::Hole(_)
                    | Value::Mark { .. } => return Ok(Atom::Other(node)),
                }
            },
            | Node::Held(value) => value,
            | Node::Stuck(neutral, prefix) => return self.stuck(neutral, prefix),
            | Node::ValueType(..) | Node::CompType(..) => return Ok(Atom::Other(node)),
        };
        let stood = Node::Held(held);
        match *self.domain.value(held).ok_or(dangling)? {
            | DomainValue::Constructor { .. }
            | DomainValue::Record { .. }
            | DomainValue::Tuple { .. }
            | DomainValue::ListNil { .. }
            | DomainValue::ListCons { .. }
            | DomainValue::Literal { .. }
            | DomainValue::Injection { .. } => Ok(Atom::FirstOrder(stood)),
            | DomainValue::Neutral { neutral, .. } => {
                let stuck = self.domain.neutral(neutral).ok_or(dangling)?;
                self.stuck(neutral, SpinePrefix(stuck.spine().len()))
            },
            | DomainValue::Code { code, .. } => {
                let closure = self.domain.value_closure(code).ok_or(dangling)?;
                let place = Self::opened(code);
                match closure.body() {
                    | crate::ValueBody::ValueType(quoted) => Ok(Atom::Quote(quoted, place)),
                    | crate::ValueBody::CompType(quoted) => {
                        Ok(Atom::QuoteComputation(quoted, place))
                    },
                    | crate::ValueBody::Source(body) => match *self
                        .core
                        .value(body)
                        .ok_or(ConversionFault::MachineInvariant)?
                    {
                        | Value::Quote(quoted) => Ok(Atom::Quote(quoted, place)),
                        | Value::QuoteComputation(quoted) => {
                            Ok(Atom::QuoteComputation(quoted, place))
                        },
                        | Value::PathRefl(_)
                        | Value::Here(_)
                        | Value::Stay(_)
                        | Value::Then(..)
                        | Value::FlowProduct(..)
                        | Value::Forward(_)
                        | Value::FunctionFlow(..)
                        | Value::SessionRelated { .. }
                        | Value::Recorded(_)
                        | Value::Funext(..)
                        | Value::Equiv(..)
                        | Value::Ua { .. }
                        | Value::Returned(_)
                        | Value::Nested(_)
                        | Value::Run(_)
                        | Value::Primitive { .. }
                        | Value::Constructor { .. }
                        | Value::Record(_)
                        | Value::PathProduct(..)
                        | Value::PathEquiv { .. }
                        | Value::Variable { .. }
                        | Value::Constant(_)
                        | Value::Reify(_)
                        | Value::ListNil
                        | Value::ListCons(..)
                        | Value::Tuple(_)
                        | Value::Literal(_)
                        | Value::Injection(..)
                        | Value::Thunk(_)
                        | Value::Lift { .. }
                        | Value::StaticLambda(_)
                        | Value::StaticApplication(..)
                        | Value::Hole(_)
                        | Value::Mark { .. } => Ok(Atom::Other(stood)),
                    },
                }
            },
            | DomainValue::StaticLambda { lambda, .. } => {
                let closure = self.domain.value_closure(lambda).ok_or(dangling)?;
                let crate::ValueBody::Source(body) = closure.body()
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                Ok(Atom::Operator(body, Self::opened(lambda)))
            },
            | DomainValue::PathCertificate { .. }
            | DomainValue::PathProduct { .. }
            | DomainValue::Here { .. }
            | DomainValue::Flow { .. }
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
    ///   arity. A prefix past the spine and a removed neutral refuse
    ///   distinctly; shortening by more than one or forgetting the prefix
    ///   changes those observations.
    /// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
    /// - witness: `code::tests::stuck_prefixes_distinguish_heads_eliminations_and_refusals`
    #[spec(ensures: |ret| self.domain.neutral(neutral).map_or_else(
        || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        |held| if prefix.0 == 0 {
            match held.head() {
                NeutralHead::Variable { zone, level } => ret == Ok(Atom::Variable(zone, level)),
                NeutralHead::Constant(constant) => ret == Ok(Atom::Constant(constant,
                    if matches!(held.unfolding(), Unfolding::Rigid) { Rigidity::Rigid } else { Rigidity::Flexible })),
                NeutralHead::Module(_) | NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_) => ret == Ok(Atom::Other(Node::Stuck(neutral, prefix))),
            }
        } else {
            match held.spine().get(prefix.0.saturating_sub(1)) {
                Some(&Elimination::StaticApply(argument)) => ret == Ok(Atom::Applied(Node::Stuck(neutral, SpinePrefix(prefix.0.saturating_sub(1))), Node::Held(argument))),
                Some(_) => ret == Ok(Atom::Other(Node::Stuck(neutral, prefix))),
                None => ret == Err(ConversionFault::MachineInvariant),
            }
        }))]
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
                | NeutralHead::Module(_)
                | NeutralHead::Hole { .. }
                | NeutralHead::Mark { .. }
                | NeutralHead::Returned(_) => Atom::Other(Node::Stuck(neutral, prefix)),
            });
        };
        match held.spine().get(last) {
            | Some(&Elimination::StaticApply(argument)) => Ok(Atom::Applied(
                Node::Stuck(neutral, SpinePrefix(last)),
                Node::Held(argument),
            )),
            | Some(
                &(Elimination::Transport(_)
                | Elimination::DataCase(_)
                | Elimination::Split(_)
                | Elimination::Projection(_)
                | Elimination::ProductTransport(_)
                | Elimination::PathTransport { .. }
                | Elimination::Ride { .. }
                | Elimination::TelescopeTransport { .. }
                | Elimination::Apply(_)
                | Elimination::Force
                | Elimination::Bind(_)
                | Elimination::ListFold { .. }
                | Elimination::Case { .. }
                | Elimination::Fixpoint(_)),
            ) => Ok(Atom::Other(Node::Stuck(neutral, prefix))),
            | None => Err(ConversionFault::MachineInvariant),
        }
    }

    /// Whether a constant the core names can unfold here.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: flexible without definitions; with definitions, rigid exactly
    ///   when the constant has no unfolding body.
    /// - provides: the conservative constant reading shared by both passes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unread constants leave a mismatch undecided, known
    ///   opaque constants permit a rigid refutation, and a constant with a body
    ///   remains flexible. Treating absence of definitions as opacity or a body
    ///   as rigid changes the verdict.
    /// - witness: `code::tests::a_quote_over_a_defined_constant_is_undecided`
    /// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
    #[spec(ensures: |ret| match self.constants {
        ConstantReading::Unread => ret == Rigidity::Flexible,
        ConstantReading::Read(definitions) => (ret == Rigidity::Rigid) == matches!(definitions.unfolding(constant), Unfolding::Rigid),
    })]
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
    /// # Adequacy
    /// - hypothesis: L3 — separate quotes of one dependent type agree, changing
    ///   a rigid former or lift level separates them, and the same written
    ///   variable can agree or differ according to its captured environment.
    ///   The predicate pins root atom decisions and reflexivity; the witnesses
    ///   separate nested binders, decoding and static application.
    /// - witness: `code::tests::two_quotes_of_one_type_are_equal`
    /// - witness: `code::tests::rigid_quotes_of_different_types_are_apart`
    /// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
    /// - witness: `code::tests::a_decode_of_a_held_quote_compares_as_its_quoted_type`
    /// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
    ///
    /// # Errors
    /// As [`Walk::atom`].
    #[spec(ensures: |ret| {
        let roots = self.closure_atom(left).and_then(|one| self.closure_atom(right).map(|other| (one, other)));
        match roots {
            Err(fault) => ret == Err(fault),
            Ok((one, other)) => match (one, other) {
                (Atom::Quote(..), Atom::Quote(..)) | (Atom::QuoteComputation(..), Atom::QuoteComputation(..))
                | (Atom::Lift(..), Atom::Lift(..)) | (Atom::Applied(..), Atom::Applied(..))
                | (Atom::Operator(..),Atom::Operator(..)) | (Atom::FirstOrder(_),Atom::FirstOrder(_)) =>
                    matches!(ret, Ok(_) | Err(ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant))
                        && (left != right || ret.is_err() || ret == Ok(Alike::Same)),
                (Atom::Local(a), Atom::Local(b)) => ret == Ok(Alike::between(&a, &b)),
                (Atom::Variable(zone, a), Atom::Variable(other_zone, b)) => ret == Ok(Alike::between(&(zone, a), &(other_zone, b))),
                (Atom::Constant(a, _), Atom::Constant(b, _)) => ret == Ok(Alike::between(&a, &b)),
                (Atom::Other(a), Atom::Other(b)) => ret == Ok(Alike::between(&a, &b)),
                _ => ret == Ok(Alike::Different),
            },
        }
    })]
    fn equal(
        &mut self,
        left: ValueClosureId,
        right: ValueClosureId,
    ) -> Result<Alike, ConversionFault>
    {
        self.equal_atoms(self.closure_atom(left)?, self.closure_atom(right)?)
    }

    /// The atom a closure's own body reads as.
    ///
    /// # Specification
    /// - requires: the closure belongs to this run's domain and core arenas.
    /// - ensures: the atom of its body at its own environment and an empty
    ///   local binder chain.
    /// - provides: the root reading shared by equality and rigidity.
    /// - fails: dangling for an absent closure, otherwise as [`Walk::atom`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a live closure resolves its own quoted body and
    ///   environment, while a removed closure refuses before its core body can
    ///   be read; using another closure or bypassing resolution changes
    ///   comparison or refusal.
    /// - witness: `code::tests::atom_resolution_refuses_missing_sources_and_preserves_zone`
    /// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
    #[spec(ensures: |ret| self.domain.value_closure(closure).map_or_else(
        || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        |held| match held.body() {
            crate::ValueBody::Source(body) => ret == self.atom(Node::Code(body,Self::opened(closure))),
            crate::ValueBody::ValueType(body) => ret == Ok(Atom::Quote(body,Self::opened(closure))),
            crate::ValueBody::CompType(body) => ret == Ok(Atom::QuoteComputation(body,Self::opened(closure))),
        }))]
    fn closure_atom(
        &self,
        closure: ValueClosureId,
    ) -> Result<Atom, ConversionFault>
    {
        let held = self
            .domain
            .value_closure(closure)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        match held.body() {
            | crate::ValueBody::Source(body) => self.atom(Node::Code(body, Self::opened(closure))),
            | crate::ValueBody::ValueType(body) => Ok(Atom::Quote(body, Self::opened(closure))),
            | crate::ValueBody::CompType(body) => {
                Ok(Atom::QuoteComputation(body, Self::opened(closure)))
            },
        }
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
    ///   of a held quote, and a decode beside a type it is not. Stopping before
    ///   a held quote is decoded, or crossing into the wrong type family,
    ///   changes which independently written types agree.
    /// - witness: `code::tests::a_decode_of_a_held_quote_compares_as_its_quoted_type`
    #[spec(ensures: |ret| match ret {
        Ok(Node::ValueType(at, place)) => matches!(node, Node::ValueType(..)) && match self.core.value_type(at) {
            Some(&ValueType::Element { code, .. }) => !matches!(self.atom(Node::Code(code, place)), Ok(Atom::Quote(..))),
            Some(_) => true,
            None => false,
        },
        Ok(Node::CompType(at, place)) => matches!(node, Node::CompType(..)) && match self.core.comp_type(at) {
            Some(&CompType::Element { code, .. }) => !matches!(self.atom(Node::Code(code, place)), Ok(Atom::QuoteComputation(..))),
            Some(_) => true,
            None => false,
        },
        Ok(other) => other == node,
        Err(fault) => matches!(fault, ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant),
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
                    | ValueType::PathUniverse(..)
                    | ValueType::Capability { .. }
                    | ValueType::Path { .. }
                    | ValueType::Data { .. }
                    | ValueType::Record(_)
                    | ValueType::Stack { .. }
                    | ValueType::Base(_)
                    | ValueType::Product(..)
                    | ValueType::Sigma { .. }
                    | ValueType::Sum(..)
                    | ValueType::List(_)
                    | ValueType::Thunk(_)
                    | ValueType::Universe { .. }
                    | ValueType::Lift { .. }
                    | ValueType::Abstract(_)
                    | ValueType::StaticPi { .. }
                    | ValueType::Unknown
                    | ValueType::Session(_)
                    | ValueType::Flow { .. }
                    | ValueType::Run(_) => return Ok(node),
                },
                | Node::CompType(at, place) => match *self
                    .core
                    .comp_type(at)
                    .ok_or(ConversionFault::MachineInvariant)?
                {
                    | CompType::Element { code, .. } => (code, place),
                    | CompType::Returner { .. }
                    | CompType::With(..)
                    | CompType::Arrow { .. }
                    | CompType::Pi { .. }
                    | CompType::Unknown => {
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
    ///   codomain and a dependent pair's second factor one shared binder
    ///   further in.
    /// - provides: the per-former step of the first pass.
    /// - fails: [`ConversionFault::MachineInvariant`] when a node does not
    ///   resolve, without appending partial child obligations.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent arrow is equal only when its domain and
    ///   bound codomain agree, unequal rigid formers and lift levels separate,
    ///   and decoded held quotes compare as their types. The predicate pins
    ///   payload decisions and the number of queued premises; omitting a child
    ///   or crossing the codomain under the wrong binder changes the witnesses.
    /// - witness: `code::tests::two_quotes_of_one_type_are_equal`
    /// - witness: `code::tests::rigid_quotes_of_different_types_are_apart`
    /// - witness: `code::tests::a_decode_of_a_held_quote_compares_as_its_quoted_type`
    /// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
    /// - witness: `code::tests::native_classifier_endpoints_compare_in_order_and_refuse_a_missing_target`
    ///
    /// # Errors
    /// As above, and as [`Walk::atom`].
    #[spec(
        captures: [entry_nodes = pending.len(), entry_atoms = atoms.len()],
        ensures: |ret| {
            let roots = self.decoded(one).and_then(|left| self.decoded(other).map(|right| (left, right)));
            let mut children_correct = true;
            let expected = match roots {
                Err(fault) => Err(fault),
                Ok((Node::ValueType(first, here), Node::ValueType(second, there))) => match (self.core.value_type(first), self.core.value_type(second)) {
(Some(left), Some(right)) => {
if let ValueType::Data { declaration: ref a, arguments: ref left } = *left
&& let ValueType::Data { declaration: ref b, arguments: ref right } = *right {
if a != b || left.len() != right.len() { Ok((Alike::Different,0,0)) }
else { children_correct = pending.get(entry_nodes..).is_some_and(|added| added.iter().copied().eq(left.iter().zip(right).map(|(a,b)| (Node::Code(*a,here),Node::Code(*b,there))))); Ok((Alike::Same,left.len(),0)) }
} else if let ValueType::Record(ref left) = *left && let ValueType::Record(ref right) = *right {
if left.keys().eq(right.keys()) { children_correct = pending.get(entry_nodes..).is_some_and(|added| added.iter().copied().eq(left.values().zip(right.values()).map(|(a,b)| (Node::ValueType(*a,here),Node::ValueType(*b,there))))); Ok((Alike::Same,left.len(),0)) } else { Ok((Alike::Different,0,0)) }
} else if let (&ValueType::Product(ref left), &ValueType::Product(ref right)) | (&ValueType::Sum(ref left), &ValueType::Sum(ref right)) = (left, right) {
if left.len() == right.len() { children_correct = pending.get(entry_nodes..).is_some_and(|added| added.iter().rev().copied().eq(left.iter().zip(right.iter()).map(|(a,b)| (Node::ValueType(*a,here),Node::ValueType(*b,there))))); Ok((Alike::Same,left.len(),0)) } else { Ok((Alike::Different,0,0)) }
} else if let ValueType::Session(ref a) = *left && let ValueType::Session(ref b) = *right {
if a.protocol() == b.protocol() && a.state() == b.state() { children_correct = pending.get(entry_nodes..).is_some_and(|added| added.iter().rev().copied().eq(a.payloads().iter().zip(b.payloads()).map(|(a, b)| (Node::ValueType(*a, here), Node::ValueType(*b, there))))); Ok((Alike::Same, a.payloads().len(), 0)) } else { Ok((Alike::Different, 0, 0)) }
} else { match (left, right) {
                        (&ValueType::PathUniverse(a, b), &ValueType::PathUniverse(c, d)) =>
                            self.atom(Node::Code(a, here)).and_then(|first_left| {
                                let first_right = self.atom(Node::Code(c, there))?;
                                let second_left = self.atom(Node::Code(b, here))?;
                                let second_right = self.atom(Node::Code(d, there))?;
                                Ok([(first_left, first_right), (second_left, second_right)])
                            }).map(|expected| { children_correct = atoms.get(entry_atoms..) == Some(expected.as_slice()); (Alike::Same, 0, 2) }),
                        (&ValueType::Base(a), &ValueType::Base(b)) => Ok((Alike::between(&a, &b), 0, 0)),
                        (&ValueType::Abstract(a), &ValueType::Abstract(b)) => Ok((Alike::between(&a, &b), 0, 0)),
                        (&ValueType::Universe { .. }, &ValueType::Universe { .. }) => Ok((Alike::between(left, right), 0, 0)),
                        (&ValueType::Stack { .. }, &ValueType::Stack { .. })
                        | (&ValueType::StaticPi { .. }, &ValueType::StaticPi { .. })
                        | (&ValueType::Sigma { .. }, &ValueType::Sigma { .. }) => Ok((Alike::Same, 2, 0)),
                        (&ValueType::List(_), &ValueType::List(_)) | (&ValueType::Thunk(_), &ValueType::Thunk(_)) => Ok((Alike::Same, 1, 0)),
                        (&ValueType::Lift { inner, ref target }, &ValueType::Lift { inner: other_inner, target: ref other_target }) => {
                            if target == other_target {
                                children_correct = pending.last().is_some_and(|&(left, right)| matches!((left, right),
                                    (Node::ValueType(a, _), Node::ValueType(b, _)) if a == inner && b == other_inner));
                                Ok((Alike::Same, 1, 0))
                            } else { Ok((Alike::Different, 0, 0)) }
                        },
                        (&ValueType::Element { code, ref target }, &ValueType::Element { code: other_code, target: ref other_target }) => {
                            if target != other_target { Ok((Alike::Different, 0, 0)) }
                            else if let Ok((Node::ValueType(_, here), Node::ValueType(_, there))) = roots {
                                self.atom(Node::Code(code, here)).and_then(|_| self.atom(Node::Code(other_code, there))).map(|_| (Alike::Same, 0, 1))
                            } else { Err(ConversionFault::MachineInvariant) }
                        },
                        (&ValueType::Flow { source: a, target: b, .. }, &ValueType::Flow { source: c, target: d, .. }) =>
                            self.atom(Node::Code(a, here)).and_then(|first_left| {
                                let first_right = self.atom(Node::Code(c, there))?;
                                let second_left = self.atom(Node::Code(b, here))?;
                                let second_right = self.atom(Node::Code(d, there))?;
                                Ok([(first_left, first_right), (second_left, second_right)])
                            }).map(|expected| { children_correct = atoms.get(entry_atoms..) == Some(expected.as_slice()); (Alike::Same, 1, 2) }),
                        (&ValueType::Path { left: a, right: b, .. }, &ValueType::Path { left: c, right: d, .. }) =>
                            self.atom(Node::Code(a, here)).and_then(|first_left| {
                                let first_right = self.atom(Node::Code(c, there))?;
                                let second_left = self.atom(Node::Code(b, here))?;
                                let second_right = self.atom(Node::Code(d, there))?;
                                Ok([(first_left, first_right), (second_left, second_right)])
                            }).map(|expected| { children_correct = atoms.get(entry_atoms..) == Some(expected.as_slice()); (Alike::Same, 1, 2) }),
                        (&ValueType::Run(a), &ValueType::Run(b)) =>
                            self.atom(Node::Code(a, here)).and_then(|left| Ok([(left, self.atom(Node::Code(b, there))?)]))
                                .map(|expected| { children_correct = atoms.get(entry_atoms..) == Some(expected.as_slice()); (Alike::Same, 0, 1) }),
                        _ => Ok((Alike::Different, 0, 0)),
} } },
                    _ => Err(ConversionFault::MachineInvariant),
                },
                Ok((Node::CompType(first, _), Node::CompType(second, _))) => match (self.core.comp_type(first), self.core.comp_type(second)) {
                    (Some(left), Some(right)) => match *left {
                        CompType::Returner { effects: ref first, .. } => match *right {
                            CompType::Returner { effects: ref second, .. } if matching_effect_shapes(first, second) == Alike::Same => Ok((Alike::Same, 1_usize.saturating_add(first.types().count()), 0)),
                            _ => Ok((Alike::Different, 0, 0)),
                        },
                        CompType::With(..) | CompType::Arrow { .. } | CompType::Pi { .. } => if core::mem::discriminant(left) == core::mem::discriminant(right) { Ok((Alike::Same, 2, 0)) } else { Ok((Alike::Different, 0, 0)) },
                        CompType::Element { code, ref target } => match *right {
                            CompType::Element { code: other_code, target: ref other_target } if target == other_target => {
                                if let Ok((Node::CompType(_, here), Node::CompType(_, there))) = roots {
                                    self.atom(Node::Code(code, here)).and_then(|_| self.atom(Node::Code(other_code, there))).map(|_| (Alike::Same, 0, 1))
                                } else { Err(ConversionFault::MachineInvariant) }
                            },
                            _ => Ok((Alike::Different, 0, 0)),
                        },
                        CompType::Unknown => Ok((Alike::Different, 0, 0)),
                    },
                    _ => Err(ConversionFault::MachineInvariant),
                },
                Ok((left @ (Node::Code(..) | Node::Held(_) | Node::Stuck(..)),right @ (Node::Code(..) | Node::Held(_) | Node::Stuck(..)))) => self.atom(left).and_then(|a| self.atom(right).map(|b| { children_correct = atoms.get(entry_atoms..) == Some(&[(a,b)]); (Alike::Same,0,1) })),
                Ok(_) => Ok((Alike::Different, 0, 0)),
            };
            children_correct && match expected {
                Ok((answer, added_nodes, added_atoms)) => ret == Ok(answer)
                    && pending.len().checked_sub(entry_nodes) == Some(added_nodes)
                    && atoms.len().checked_sub(entry_atoms) == Some(added_atoms),
                Err(fault) => ret == Err(fault) && pending.len() == entry_nodes && atoms.len() == entry_atoms,
            }
        },
    )]
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
            | (
                left @ (Node::Code(..) | Node::Held(_) | Node::Stuck(..)),
                right @ (Node::Code(..) | Node::Held(_) | Node::Stuck(..)),
            ) => {
                let pair = (self.atom(left)?, self.atom(right)?);
                atoms.push(pair);
                Ok(Alike::Same)
            },
            | (Node::ValueType(first, here), Node::ValueType(second, there)) => {
                let (Some(left), Some(right)) =
                    (self.core.value_type(first), self.core.value_type(second))
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                {
                    let (matched_left_value, matched_right_value) = (left, right);
                    if let ValueType::Data {
                        declaration: ref a,
                        arguments: ref left,
                    } = *matched_left_value
                        && let ValueType::Data {
                            declaration: ref b,
                            arguments: ref right,
                        } = *matched_right_value
                    {
                        {
                            if a != b || left.len() != right.len() {
                                return Ok(Alike::Different);
                            }
                            pending.extend(
                                left.iter()
                                    .zip(right)
                                    .map(|(a, b)| (Node::Code(*a, here), Node::Code(*b, there))),
                            );
                            Ok(Alike::Same)
                        }
                    }
                    else if let ValueType::Record(ref left) = *matched_left_value
                        && let ValueType::Record(ref right) = *matched_right_value
                    {
                        {
                            if !left.keys().eq(right.keys()) {
                                return Ok(Alike::Different);
                            }
                            pending.extend(left.values().zip(right.values()).map(|(a, b)| {
                                (Node::ValueType(*a, here), Node::ValueType(*b, there))
                            }));
                            Ok(Alike::Same)
                        }
                    }
                    else if let ValueType::Stack {
                        input: a,
                        output: b,
                    } = *matched_left_value
                        && let ValueType::Stack {
                            input: c,
                            output: d,
                        } = *matched_right_value
                    {
                        pending.extend([
                            (Node::CompType(b, here), Node::CompType(d, there)),
                            (Node::CompType(a, here), Node::CompType(c, there)),
                        ]);
                        Ok(Alike::Same)
                    }
                    else if let ValueType::Capability {
                        authority: ref first,
                        grade,
                        region,
                    } = *matched_left_value
                        && let ValueType::Capability {
                            authority: ref second,
                            grade: other_grade,
                            region: other_region,
                        } = *matched_right_value
                    {
                        if (grade, region) != (other_grade, other_region)
                            || matching_effect_shapes(first, second) == Alike::Different
                        {
                            return Ok(Alike::Different);
                        }
                        pending.extend(first.types().zip(second.types()).map(|(left, right)| {
                            (Node::ValueType(left, here), Node::ValueType(right, there))
                        }));
                        Ok(Alike::Same)
                    }
                    else if let ValueType::List(a) = *matched_left_value
                        && let ValueType::List(b) = *matched_right_value
                    {
                        pending.push((Node::ValueType(a, here), Node::ValueType(b, there)));
                        Ok(Alike::Same)
                    }
                    else if let ValueType::PathUniverse(a, b) = *matched_left_value
                        && let ValueType::PathUniverse(c, d) = *matched_right_value
                    {
                        {
                            let first = (
                                self.atom(Node::Code(a, here))?,
                                self.atom(Node::Code(c, there))?,
                            );
                            let second = (
                                self.atom(Node::Code(b, here))?,
                                self.atom(Node::Code(d, there))?,
                            );
                            atoms.extend([first, second]);
                            Ok(Alike::Same)
                        }
                    }
                    else if let ValueType::Path {
                        carrier: a,
                        left: b,
                        right: c,
                    } = *matched_left_value
                        && let ValueType::Path {
                            carrier: d,
                            left: e,
                            right: f,
                        } = *matched_right_value
                    {
                        pending.push((Node::ValueType(a, here), Node::ValueType(d, there)));
                        let left = (
                            self.atom(Node::Code(b, here))?,
                            self.atom(Node::Code(e, there))?,
                        );
                        let right = (
                            self.atom(Node::Code(c, here))?,
                            self.atom(Node::Code(f, there))?,
                        );
                        atoms.extend([left, right]);
                        Ok(Alike::Same)
                    }
                    else if let ValueType::Flow {
                        carrier: a,
                        source: b,
                        target: c,
                    } = *matched_left_value
                        && let ValueType::Flow {
                            carrier: d,
                            source: e,
                            target: f,
                        } = *matched_right_value
                    {
                        pending.push((Node::ValueType(a, here), Node::ValueType(d, there)));
                        let source = (
                            self.atom(Node::Code(b, here))?,
                            self.atom(Node::Code(e, there))?,
                        );
                        let target = (
                            self.atom(Node::Code(c, here))?,
                            self.atom(Node::Code(f, there))?,
                        );
                        atoms.extend([source, target]);
                        Ok(Alike::Same)
                    }
                    else if let ValueType::Run(a) = *matched_left_value
                        && let ValueType::Run(b) = *matched_right_value
                    {
                        let session = (
                            self.atom(Node::Code(a, here))?,
                            self.atom(Node::Code(b, there))?,
                        );
                        atoms.push(session);
                        Ok(Alike::Same)
                    }
                    else if let ValueType::Base(a) = *matched_left_value
                        && let ValueType::Base(b) = *matched_right_value
                    {
                        Ok(Alike::between(&a, &b))
                    }
                    else if let (&ValueType::Product(ref left), &ValueType::Product(ref right))
                    | (&ValueType::Sum(ref left), &ValueType::Sum(ref right)) =
                        (matched_left_value, matched_right_value)
                    {
                        if left.len() != right.len() {
                            return Ok(Alike::Different);
                        }
                        pending.extend(
                            left.iter().zip(right.iter()).rev().map(|(a, b)| {
                                (Node::ValueType(*a, here), Node::ValueType(*b, there))
                            }),
                        );
                        Ok(Alike::Same)
                    }
                    else if let ValueType::Abstract(a) = *matched_left_value
                        && let ValueType::Abstract(b) = *matched_right_value
                    {
                        Ok(Alike::between(&a, &b))
                    }
                    else if let ValueType::Universe {
                        ref sort,
                        ref level,
                    } = *matched_left_value
                        && let ValueType::Universe {
                            sort: ref other_sort,
                            level: ref other_level,
                        } = *matched_right_value
                    {
                        Ok(Alike::between(&(sort, level), &(other_sort, other_level)))
                    }
                    else if let ValueType::StaticPi {
                        domain: a,
                        codomain: b,
                    } = *matched_left_value
                        && let ValueType::StaticPi {
                            domain: c,
                            codomain: d,
                        } = *matched_right_value
                    {
                        {
                            pending.push((Node::ValueType(b, here), Node::ValueType(d, there)));
                            pending.push((Node::ValueType(a, here), Node::ValueType(c, there)));
                            Ok(Alike::Same)
                        }
                    }
                    else if let ValueType::Sigma {
                        first: a,
                        second: b,
                    } = *matched_left_value
                        && let ValueType::Sigma {
                            first: c,
                            second: d,
                        } = *matched_right_value
                    {
                        let (inside, other_inside) = self.crossed(here, there);
                        pending
                            .push((Node::ValueType(b, inside), Node::ValueType(d, other_inside)));
                        pending.push((Node::ValueType(a, here), Node::ValueType(c, there)));
                        Ok(Alike::Same)
                    }
                    else if let ValueType::Thunk(a) = *matched_left_value
                        && let ValueType::Thunk(b) = *matched_right_value
                    {
                        {
                            pending.push((Node::CompType(a, here), Node::CompType(b, there)));
                            Ok(Alike::Same)
                        }
                    }
                    else if let ValueType::Lift { inner, ref target } = *matched_left_value
                        && let ValueType::Lift {
                            inner: other_inner,
                            target: ref other_target,
                        } = *matched_right_value
                    {
                        {
                            if target != other_target {
                                return Ok(Alike::Different);
                            }
                            pending.push((
                                Node::ValueType(inner, here),
                                Node::ValueType(other_inner, there),
                            ));
                            Ok(Alike::Same)
                        }
                    }
                    else if let ValueType::Element { code, ref target } = *matched_left_value
                        && let ValueType::Element {
                            code: other_code,
                            target: ref other_target,
                        } = *matched_right_value
                    {
                        {
                            if target != other_target {
                                return Ok(Alike::Different);
                            }
                            let left_atom = self.atom(Node::Code(code, here))?;
                            let right_atom = self.atom(Node::Code(other_code, there))?;
                            atoms.push((left_atom, right_atom));
                            Ok(Alike::Same)
                        }
                    }
                    else if let ValueType::Session(ref a) = *matched_left_value
                        && let ValueType::Session(ref b) = *matched_right_value
                    {
                        if a.protocol() != b.protocol() || a.state() != b.state() {
                            return Ok(Alike::Different);
                        }
                        pending.extend(
                            a.payloads().iter().zip(b.payloads()).rev().map(|(a, b)| {
                                (Node::ValueType(*a, here), Node::ValueType(*b, there))
                            }),
                        );
                        Ok(Alike::Same)
                    }
                    else {
                        {
                            match *matched_left_value {
                                | ValueType::PathUniverse(..)
                                | ValueType::Capability { .. }
                                | ValueType::Path { .. }
                                | ValueType::Data { .. }
                                | ValueType::Record(_)
                                | ValueType::Base(_)
                                | ValueType::List(_)
                                | ValueType::Stack { .. }
                                | ValueType::Product(..)
                                | ValueType::Sum(..)
                                | ValueType::Thunk(_)
                                | ValueType::Universe { .. }
                                | ValueType::Lift { .. }
                                | ValueType::Element { .. }
                                | ValueType::Abstract(_)
                                | ValueType::StaticPi { .. }
                                | ValueType::Sigma { .. }
                                | ValueType::Unknown
                                | ValueType::Session(_)
                                | ValueType::Flow { .. }
                                | ValueType::Run(_) => Ok(Alike::Different),
                            }
                        }
                    }
                }
            },
            | (Node::CompType(first, here), Node::CompType(second, there)) => {
                let (Some(left), Some(right)) =
                    (self.core.comp_type(first), self.core.comp_type(second))
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                match (left, right) {
                    | (&CompType::With(a, b), &CompType::With(c, d)) => {
                        pending.extend([
                            (Node::CompType(b, here), Node::CompType(d, there)),
                            (Node::CompType(a, here), Node::CompType(c, there)),
                        ]);
                        Ok(Alike::Same)
                    },
                    | (
                        &CompType::Returner {
                            result: a,
                            effects: ref first,
                        },
                        &CompType::Returner {
                            result: b,
                            effects: ref second,
                        },
                    ) => {
                        if matching_effect_shapes(first, second) == Alike::Different {
                            return Ok(Alike::Different);
                        }
                        pending.push((Node::ValueType(a, here), Node::ValueType(b, there)));
                        pending.extend(first.types().zip(second.types()).map(|(left, right)| {
                            (Node::ValueType(left, here), Node::ValueType(right, there))
                        }));
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
                        &(CompType::Returner { .. }
                        | CompType::With(..)
                        | CompType::Arrow { .. }
                        | CompType::Pi { .. }
                        | CompType::Element { .. }
                        | CompType::Unknown),
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
    /// # Adequacy
    /// - hypothesis: L3 — mismatched rigid types are apart, a body-bearing or
    ///   unread constant leaves a mismatch undecided, and a static operator
    ///   stays flexible even when its body is rigid. Declaring a flexible atom
    ///   rigid would turn an undecided conversion into a refutation.
    /// - witness: `code::tests::rigid_quotes_of_different_types_are_apart`
    /// - witness: `code::tests::a_quote_over_a_defined_constant_is_undecided`
    /// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
    ///
    /// # Errors
    /// As [`Walk::atom`].
    #[spec(ensures: |ret| match self.closure_atom(closure) {
        Err(fault) => ret == Err(fault),
        Ok(Atom::Local(_) | Atom::Variable(..) | Atom::Constant(_, Rigidity::Rigid)) => ret == Ok(Rigidity::Rigid),
        Ok(Atom::Constant(_, Rigidity::Flexible) | Atom::Operator(..) | Atom::Other(_)) => ret == Ok(Rigidity::Flexible),
        Ok(Atom::Quote(id, _)) => match self.core.value_type(id) {
            None => ret == Err(ConversionFault::MachineInvariant),
            Some(&(ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_))) => ret == Ok(Rigidity::Rigid),
            Some(held) if matches!(*held, ValueType::Product(ref components) if components.is_empty()) => ret == Ok(Rigidity::Rigid),
            Some(_) => matches!(ret, Ok(_) | Err(ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant)),
        },
        Ok(_) => matches!(ret, Ok(_) | Err(ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant)),
    })]
    fn rigidity(
        &mut self,
        closure: ValueClosureId,
    ) -> Result<Rigidity, ConversionFault>
    {
        self.rigidity_atom(self.closure_atom(closure)?)
    }

    /// Resolve an ordinary argument without erasing its environment or labels.
    ///
    /// # Specification
    /// - requires: the node is an ordinary structural value.
    /// - ensures: classifier and child references keep their original capture.
    /// - fails: dangling nodes or malformed record field tables.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — captured parameters agree with literal parameters
    ///   only by value.
    /// - witness: `code::tests::native_types_compare_identity_labels_and_value_arguments`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret,Err(ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant)))]
    fn first_order(
        &self,
        node: Node,
    ) -> Result<FirstOrder<'run>, ConversionFault>
    {
        let malformed = ConversionFault::MachineInvariant;
        let dangling = ConversionFault::Domain(DomainFault::Dangling);
        match node {
            | Node::Code(value, place) => match *(self.core.value(value).ok_or(malformed)?) {
                | Value::ListNil => Ok(FirstOrder::ListNil),
                | Value::ListCons(first, second) => Ok(FirstOrder::ListCons(
                    Node::Code(first, place),
                    Node::Code(second, place),
                )),
                | Value::Literal(_) => Ok(FirstOrder::Literal(value)),
                | Value::Tuple(ref components) => Ok(FirstOrder::Tuple(ArgumentFields::Source(
                    components.iter(),
                    place,
                ))),
                | Value::Injection(ref side, ref body) => {
                    Ok(FirstOrder::Injection(*side, Node::Code(*body, place)))
                },
                | Value::Constructor {
                    ref datatype,
                    ref tag,
                    ref fields,
                } => Ok(FirstOrder::Constructor {
                    datatype: Node::ValueType(*datatype, place),
                    tag: *tag,
                    fields: ArgumentFields::Source(fields.iter(), place),
                }),
                | Value::Record(ref labels) => Ok(FirstOrder::Record {
                    labels,
                    fields: ArgumentFields::Record(labels.values(), place),
                }),
                | _ => Err(malformed),
            },
            | Node::Held(value) => match *self.domain.value(value).ok_or(dangling)? {
                | DomainValue::ListNil { .. } => Ok(FirstOrder::ListNil),
                | DomainValue::ListCons { first, second, .. } => {
                    Ok(FirstOrder::ListCons(Node::Held(first), Node::Held(second)))
                },
                | DomainValue::Literal { literal, .. } => Ok(FirstOrder::Literal(literal)),
                | DomainValue::Tuple { fields, .. } => Ok(FirstOrder::Tuple(ArgumentFields::Held(
                    self.domain
                        .fields(fields)
                        .map_err(ConversionFault::Domain)?
                        .iter(),
                ))),
                | DomainValue::Injection { summand, body, .. } => {
                    Ok(FirstOrder::Injection(summand, Node::Held(body)))
                },
                | DomainValue::Constructor {
                    datatype,
                    tag,
                    fields,
                    ..
                } => {
                    let closure = self.domain.value_closure(datatype).ok_or(dangling)?;
                    let crate::ValueBody::ValueType(classifier) = closure.body()
                    else {
                        return Err(malformed);
                    };
                    Ok(FirstOrder::Constructor {
                        datatype: Node::ValueType(classifier, Self::opened(datatype)),
                        tag,
                        fields: ArgumentFields::Held(
                            self.domain
                                .fields(fields)
                                .map_err(ConversionFault::Domain)?
                                .iter(),
                        ),
                    })
                },
                | DomainValue::Record { source, fields, .. } => {
                    let Some(matched_native_node) = self.core.value(source)
                    else {
                        return Err(malformed);
                    };
                    let Value::Record(ref labels) = *matched_native_node
                    else {
                        return Err(malformed);
                    };
                    let fields = self
                        .domain
                        .fields(fields)
                        .map_err(ConversionFault::Domain)?;
                    if labels.len() != fields.len() {
                        return Err(malformed);
                    }
                    Ok(FirstOrder::Record {
                        labels,
                        fields: ArgumentFields::Held(fields.iter()),
                    })
                },
                | _ => Err(malformed),
            },
            | _ => Err(malformed),
        }
    }

    /// Compare ordinary former payloads and queue their ordered children.
    ///
    /// # Specification
    /// - requires: both nodes denote ordinary structural values.
    /// - ensures: unequal tags, labels or literal payloads differ before child
    ///   comparison.
    /// - fails: dangling source or domain references, without partial
    ///   obligations.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh equal literals agree while changed labels and
    ///   arguments separate.
    /// - witness: `code::tests::native_types_compare_identity_labels_and_value_arguments`
    #[spec(captures:[entry=pending.len()],ensures:|ret| ret.is_ok() || pending.len() == entry)]
    fn first_order_pair(
        &self,
        left: Node,
        right: Node,
        pending: &mut Vec<(Node, Node)>,
    ) -> Result<Alike, ConversionFault>
    {
        match (self.first_order(left)?, self.first_order(right)?) {
            | (FirstOrder::ListNil, FirstOrder::ListNil) => Ok(Alike::Same),
            | (FirstOrder::Tuple(left_fields), FirstOrder::Tuple(right_fields))
                if left_fields.len() == right_fields.len() =>
            {
                pending.extend(left_fields.zip(right_fields));
                Ok(Alike::Same)
            },
            | (FirstOrder::Literal(a), FirstOrder::Literal(b)) => {
                let (Some(left_node), Some(right_node)) = (self.core.value(a), self.core.value(b))
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                let Value::Literal(ref a) = *left_node
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                let Value::Literal(ref b) = *right_node
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                Ok(Alike::between(a, b))
            },
            | (FirstOrder::ListCons(a, b), FirstOrder::ListCons(c, d)) => {
                pending.extend([(a, c), (b, d)]);
                Ok(Alike::Same)
            },
            | (FirstOrder::Injection(a, b), FirstOrder::Injection(c, d)) if a == c => {
                pending.push((b, d));
                Ok(Alike::Same)
            },
            | (
                FirstOrder::Constructor {
                    datatype: left_datatype,
                    tag: left_tag,
                    fields: left_fields,
                },
                FirstOrder::Constructor {
                    datatype: right_datatype,
                    tag: right_tag,
                    fields: right_fields,
                },
            ) if left_tag == right_tag && left_fields.len() == right_fields.len() => {
                pending.extend(left_fields.zip(right_fields));
                pending.push((left_datatype, right_datatype));
                Ok(Alike::Same)
            },
            | (
                FirstOrder::Record {
                    labels: a,
                    fields: b,
                },
                FirstOrder::Record {
                    labels: c,
                    fields: d,
                },
            ) if a.keys().eq(c.keys()) => {
                pending.extend(b.zip(d));
                Ok(Alike::Same)
            },
            | _ => Ok(Alike::Different),
        }
    }

    /// Compare quoted roots or structural argument roots on the same iterative
    /// worklist.
    ///
    /// # Specification
    /// - requires: roots belong to the held arenas.
    /// - ensures: equal live roots compare reflexively; every queued child must
    ///   also agree.
    /// - fails: a dangling child or malformed source.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nominal identities and unequal ordinary arguments
    ///   separate.
    /// - witness: `code::tests::native_types_compare_identity_labels_and_value_arguments`
    #[spec(ensures: |ret| left_atom != right_atom || ret.is_err() || ret == Ok(Alike::Same))]
    fn equal_atoms(
        &mut self,
        left_atom: Atom,
        right_atom: Atom,
    ) -> Result<Alike, ConversionFault>
    {
        let mut pending: Vec<(Node, Node)> = Vec::new();
        let mut atoms = Vec::from([(left_atom, right_atom)]);
        loop {
            while let Some((one, other)) = atoms.pop() {
                match (one, other) {
                    | (Atom::FirstOrder(first), Atom::FirstOrder(second)) => {
                        if self.first_order_pair(first, second, &mut pending)? == Alike::Different {
                            return Ok(Alike::Different);
                        }
                    },
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
                        | Atom::FirstOrder(_)
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

    /// Inspect every structural type or ordinary argument below a root.
    ///
    /// # Specification
    /// - requires: the root resolves in the held arenas.
    /// - ensures: unhandled computation-bearing arguments remain flexible,
    ///   never a rigid refutation.
    /// - fails: dangling or malformed children.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nominal arguments contribute their own rigidity.
    /// - witness: `code::tests::native_types_compare_identity_labels_and_value_arguments`
    #[spec(ensures: |ret| !matches!(root,Atom::Other(_) | Atom::Operator(..) | Atom::Constant(_,Rigidity::Flexible)) || ret == Ok(Rigidity::Flexible))]
    fn rigidity_atom(
        &mut self,
        root: Atom,
    ) -> Result<Rigidity, ConversionFault>
    {
        let mut atoms = Vec::from([root]);
        let mut types: Vec<Node> = Vec::new();
        while !atoms.is_empty() || !types.is_empty() {
            while let Some(atom) = atoms.pop() {
                match atom {
                    | Atom::FirstOrder(node) => match self.first_order(node)? {
                        | FirstOrder::ListNil | FirstOrder::Literal(_) => {},
                        | FirstOrder::ListCons(a, b) => {
                            atoms.push(self.atom(a)?);
                            atoms.push(self.atom(b)?);
                        },
                        | FirstOrder::Injection(_, body) => atoms.push(self.atom(body)?),
                        | FirstOrder::Constructor {
                            datatype, fields, ..
                        } => {
                            types.push(datatype);
                            for field in fields {
                                atoms.push(self.atom(field)?);
                            }
                        },
                        | FirstOrder::Record { fields, .. } | FirstOrder::Tuple(fields) => {
                            for field in fields {
                                atoms.push(self.atom(field)?);
                            }
                        },
                    },
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
                        | ValueType::Data { ref arguments, .. } => {
                            for argument in arguments {
                                atoms.push(self.atom(Node::Code(*argument, place))?);
                            }
                        },
                        | ValueType::Record(ref fields) => types
                            .extend(fields.values().map(|field| Node::ValueType(*field, place))),
                        | ValueType::Stack { input, output } => types
                            .extend([Node::CompType(input, place), Node::CompType(output, place)]),
                        | ValueType::List(element) => types.push(Node::ValueType(element, place)),
                        | ValueType::PathUniverse(source, target) => {
                            atoms.push(self.atom(Node::Code(source, place))?);
                            atoms.push(self.atom(Node::Code(target, place))?);
                        },
                        | ValueType::Path {
                            carrier,
                            left,
                            right,
                        } => {
                            types.push(Node::ValueType(carrier, place));
                            atoms.push(self.atom(Node::Code(left, place))?);
                            atoms.push(self.atom(Node::Code(right, place))?);
                        },
                        | ValueType::Flow {
                            carrier,
                            source,
                            target,
                        } => {
                            types.push(Node::ValueType(carrier, place));
                            atoms.push(self.atom(Node::Code(source, place))?);
                            atoms.push(self.atom(Node::Code(target, place))?);
                        },
                        | ValueType::Run(session) => {
                            atoms.push(self.atom(Node::Code(session, place))?);
                        },
                        | ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                            types.extend(
                                components
                                    .iter()
                                    .map(|component| Node::ValueType(*component, place)),
                            );
                        },
                        | ValueType::Base(_)
                        | ValueType::Universe { .. }
                        | ValueType::Abstract(_) => {},
                        | ValueType::Capability { ref authority, .. } => {
                            types.extend(authority.types().map(|ty| Node::ValueType(ty, place)));
                        },
                        // An unknown type is what a fill may still decide, so
                        // nothing that holds one is apart from anything.
                        | ValueType::Unknown => return Ok(Rigidity::Flexible),
                        | ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        } => {
                            types.push(Node::ValueType(first, place));
                            types.push(Node::ValueType(second, place));
                        },
                        | ValueType::Sigma { first, second } => {
                            types.push(Node::ValueType(first, place));
                            let inside = self.crossed_alone(place);
                            types.push(Node::ValueType(second, inside));
                        },
                        | ValueType::Thunk(body) => types.push(Node::CompType(body, place)),
                        | ValueType::Lift { inner, .. } => {
                            types.push(Node::ValueType(inner, place));
                        },
                        | ValueType::Element { code, .. } => {
                            atoms.push(self.atom(Node::Code(code, place))?);
                        },
                        | ValueType::Session(ref session) => types.extend(
                            session
                                .payloads()
                                .iter()
                                .map(|payload| Node::ValueType(*payload, place)),
                        ),
                    }
                },
                | Node::CompType(id, place) => {
                    match *self
                        .core
                        .comp_type(id)
                        .ok_or(ConversionFault::MachineInvariant)?
                    {
                        | CompType::With(first, second) => types
                            .extend([Node::CompType(first, place), Node::CompType(second, place)]),
                        | CompType::Returner {
                            result,
                            ref effects,
                        } => {
                            types.push(Node::ValueType(result, place));
                            types.extend(effects.types().map(|ty| Node::ValueType(ty, place)));
                        },
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
                        | CompType::Unknown => return Ok(Rigidity::Flexible),
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

/// Match interface and operation names before comparing their scoped types.
///
/// # Specification
/// - ensures: [`Alike::Same`] exactly when the rows have the same interface and
///   operation coverage.
/// - provides: only the rigid row shape, never equality of operation types.
///
/// # Adequacy
/// - hypothesis: L3 — changing names or an operation type separates distinct
///   code comparisons; separately allocated equal rows still compare equal.
/// - witness: `code::tests::effect_rows_compare_names_and_scoped_operation_types`
#[spec(ensures: |ret| ret == Alike::Different || first.signatures().len() == second.signatures().len())]
fn matching_effect_shapes(
    first: &gandr_core_term::effect::EffectRow,
    second: &gandr_core_term::effect::EffectRow,
) -> Alike
{
    let same = first.signatures().len() == second.signatures().len()
        && first
            .signatures()
            .zip(second.signatures())
            .all(|(left, right)| {
                left.name() == right.name()
                    && left.operations().len() == right.operations().len()
                    && left
                        .operations()
                        .zip(right.operations())
                        .all(|(left, right)| left.name == right.name)
            });
    if same { Alike::Same } else { Alike::Different }
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
///   operators alike and unlike. Treating every unequal pair as apart would
///   refute a flexible constant or operator, while comparing ids alone would
///   miss separately written equal types; both mutations change the observed
///   answer.
/// - witness: `code::tests::two_quotes_of_one_type_are_equal`
/// - witness: `code::tests::rigid_quotes_of_different_types_are_apart`
/// - witness: `code::tests::a_quote_over_a_defined_constant_is_undecided`
/// - witness: `code::tests::static_operators_compare_by_binder_and_spine`
/// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
/// - witness: `code::tests::a_decode_of_a_held_quote_compares_as_its_quoted_type`
#[spec(ensures: |ret| {
    let mut comparison = Walk::new(core, domain, constants);
    match comparison.equal(left, right) {
        Ok(Alike::Same) => ret == Ok(CodeComparison::Equal),
        Ok(Alike::Different) => match comparison.rigidity(left).and_then(|one| comparison.rigidity(right).map(|other| (one, other))) {
            Ok((Rigidity::Rigid, Rigidity::Rigid)) => ret == Ok(CodeComparison::Apart),
            Ok(_) => ret == Ok(CodeComparison::Undecided),
            Err(fault) => ret == Err(fault),
        },
        Err(fault) => ret == Err(fault),
    }
})]
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

    use anodized::spec;
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — one written variable closes over different domain
    ///   values, while different written indices close over the same value
    ///   through different environment depths; reversing the supplied binding
    ///   order or losing a binding changes which codes agree.
    /// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
    #[spec(ensures: |ret| domain.value_closure(ret).is_some_and(|closure| closure.body() == crate::ValueBody::Source(quote)
        && bound.iter().rev().enumerate().all(|(index, value)| u32::try_from(index).is_ok_and(|index|
            closure.environment().lookup(Zone::Intuitionistic, DeBruijnIndex::from(index)) == Some(*value))))) ]
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
    fn effect_rows_compare_names_and_scoped_operation_types()
    {
        use gandr_core_term::effect::EffectName;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let integer = core.value_type_base(BaseType::Integer);
        let unit_quote = core.value_quote(unit);
        let integer_quote = core.value_quote(integer);
        let index = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let parameter = core.value_type_element(index, Level::zero());
        let mut quoted = |effect: &str, operation: &str, reply| {
            let signature = EffectSig::new(EffectName::from(effect), alloc::vec![EffectOp {
                name: OperationName::from(operation),
                payload: unit,
                reply
            }])
            .unwrap();
            let result =
                core.comp_type_returner_with_effects(unit, EffectRow::singleton(signature));
            core.value_quote_computation(result)
        };
        let dependent = quoted("State", "get", parameter);
        let concrete = quoted("State", "get", unit);
        let other_effect = quoted("Other", "get", unit);
        let other_operation = quoted("State", "put", unit);
        let mut domain = DomainArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let held_unit = eval_value_within(
            &core,
            &mut domain,
            definitions,
            Fuel::from(64_u32),
            unit_quote,
            Environment::new(),
        )
        .unwrap()
        .0;
        let held_integer = eval_value_within(
            &core,
            &mut domain,
            definitions,
            Fuel::from(64_u32),
            integer_quote,
            Environment::new(),
        )
        .unwrap()
        .0;
        let at_unit = code_of(&core, &mut domain, dependent, &[held_unit]);
        let at_integer = code_of(&core, &mut domain, dependent, &[held_integer]);
        let written = code_of(&core, &mut domain, concrete, &[]);
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, at_unit, written)
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, at_integer, written)
        );
        for changed in [other_effect, other_operation] {
            let changed = code_of(&core, &mut domain, changed, &[]);
            assert_eq!(
                CodeComparison::Apart,
                compare_rigidly(&core, &domain, at_unit, changed)
            );
        }
    }

    #[test]
    fn control_type_codes_compare_distinct_inputs_and_outputs()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let integer = core.value_type_base(BaseType::Integer);
        let returned_integer = core.comp_type_returner(integer);
        let unit_quote = core.value_quote(unit);
        let integer_quote = core.value_quote(integer);
        let index = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let parameter = core.value_type_element(index, Level::zero());
        let mut quote = |element, reverse| {
            let list = core.value_type_list(element);
            let input = core.comp_type_returner(list);
            let output = if reverse {
                core.comp_type_with(input, returned_integer)
            }
            else {
                core.comp_type_with(returned_integer, input)
            };
            let stack = core.value_type_stack(input, output);
            core.value_quote(stack)
        };
        let dependent = quote(parameter, false);
        let concrete = quote(unit, false);
        let reversed = quote(unit, true);
        let mut domain = DomainArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let held_unit = eval_value_within(
            &core,
            &mut domain,
            definitions,
            Fuel::from(64_u32),
            unit_quote,
            Environment::new(),
        )
        .unwrap()
        .0;
        let held_integer = eval_value_within(
            &core,
            &mut domain,
            definitions,
            Fuel::from(64_u32),
            integer_quote,
            Environment::new(),
        )
        .unwrap()
        .0;
        let at_unit = code_of(&core, &mut domain, dependent, &[held_unit]);
        let at_integer = code_of(&core, &mut domain, dependent, &[held_integer]);
        let written = code_of(&core, &mut domain, concrete, &[]);
        let reversed = code_of(&core, &mut domain, reversed, &[]);
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, at_unit, written)
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, at_integer, written)
        );
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, at_unit, reversed)
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
        let squared = core.value_type_product(&[decoded, decoded]);
        let squared_quote = core.value_quote(squared);
        let written = core.value_type_product(&[integer, integer]);
        let written_quote = core.value_quote(written);
        let acting = core.comp_type_element(bound, Level::zero());
        let acting_quote = core.value_quote_computation(acting);
        let string = core.value_type_base(BaseType::String);
        let other = core.value_type_product(&[integer, string]);
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

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn binder_numbers_stay_distinct_across_the_u32_boundary()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let quote = core.value_quote(unit);
        let mut domain = DomainArena::new();
        let closure =
            domain.value_closure_node(crate::ValueBody::Source(quote), Environment::new());
        let place = super::Walk::opened(closure);
        let mut walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
        walk.next = super::Binder(
            usize::try_from(u32::MAX).expect("a 64-bit index holds the 32-bit ceiling"),
        );
        let (first, paired) = walk.crossed(place, place);
        let second = walk.crossed_alone(first);
        let at_zero = DeBruijnIndex::from(0_u32);
        assert_eq!(
            walk.local(first.chain, at_zero),
            walk.local(paired.chain, at_zero)
        );
        assert_ne!(
            walk.local(first.chain, at_zero),
            walk.local(second.chain, at_zero),
            "a fresh binder must not alias the preceding one at the 32-bit ceiling"
        );
        assert_eq!(
            walk.local(first.chain, at_zero),
            walk.local(second.chain, DeBruijnIndex::from(1_u32))
        );
    }

    #[test]
    fn local_binders_shadow_only_their_own_chain()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let quote = core.value_quote(unit);
        let mut domain = DomainArena::new();
        let closure =
            domain.value_closure_node(crate::ValueBody::Source(quote), Environment::new());
        let place = super::Walk::opened(closure);
        let mut walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
        let old = walk.crossed_alone(place);
        let (left, right) = walk.crossed(old, place);
        let zero = DeBruijnIndex::from(0_u32);
        let one = DeBruijnIndex::from(1_u32);
        assert_eq!(walk.local(left.chain, zero), walk.local(right.chain, zero));
        assert_ne!(walk.local(left.chain, zero), walk.local(left.chain, one));
        assert_eq!(walk.local(old.chain, zero), walk.local(left.chain, one));
        assert_eq!(Err(zero), walk.local(right.chain, one));
        assert_eq!(
            Err(zero),
            walk.local(left.chain, DeBruijnIndex::from(2_u32))
        );
        assert_eq!(
            Err(one),
            walk.local(right.chain, DeBruijnIndex::from(2_u32))
        );
        assert_eq!(
            Err(DeBruijnIndex::from(u32::MAX - 2)),
            walk.local(left.chain, DeBruijnIndex::from(u32::MAX))
        );
        assert_eq!(
            Err(DeBruijnIndex::from(u32::MAX)),
            walk.local(place.chain, DeBruijnIndex::from(u32::MAX))
        );
        assert_eq!(Err(one), walk.local(super::Chain(usize::MAX), one));
    }

    #[test]
    fn atom_resolution_refuses_missing_sources_and_preserves_zone()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let quote = core.value_quote(unit);
        let int_zero = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let int_one = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let int_two = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let linear_zero = core.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        let core_floor = core.watermark();
        let absent_core = core.value_unit();
        core.truncate_to(core_floor);
        let mut domain = DomainArena::new();
        let int_head = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: BinderLevel::from(9_u32),
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a variable is rigid");
        let int_value = domain
            .value_neutral(int_head, TermFace::Reduced)
            .expect("an empty spine is a value");
        let linear_head = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Linear,
                    level: BinderLevel::from(4_u32),
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a variable is rigid");
        let linear_value = domain
            .value_neutral(linear_head, TermFace::Reduced)
            .expect("an empty spine is a value");
        let before_closures = domain.watermark();
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, int_value);
        environment.extend(Zone::Linear, linear_value);
        let closure = domain.value_closure_node(crate::ValueBody::Source(quote), environment);
        let empty = domain.value_closure_node(crate::ValueBody::Source(quote), Environment::new());
        let before_absent = domain.watermark();
        let absent_held = domain.value_unit(TermFace::Reduced);
        domain.truncate_to(before_absent);
        let place = super::Walk::opened(closure);
        {
            let mut walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
            let inside = walk.crossed_alone(place);
            let local = walk
                .local(inside.chain, DeBruijnIndex::from(0_u32))
                .expect("the local binder exists");
            assert_eq!(
                Ok(super::Atom::Local(local)),
                walk.atom(super::Node::Code(int_zero, inside))
            );
            assert_eq!(
                Ok(super::Atom::Variable(
                    Zone::Intuitionistic,
                    BinderLevel::from(9_u32)
                )),
                walk.atom(super::Node::Code(int_one, inside))
            );
            assert_eq!(
                Ok(super::Atom::Variable(
                    Zone::Linear,
                    BinderLevel::from(4_u32)
                )),
                walk.atom(super::Node::Code(linear_zero, inside))
            );
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                walk.atom(super::Node::Code(int_two, inside))
            );
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                walk.atom(super::Node::Code(int_zero, super::Walk::opened(empty)))
            );
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                walk.atom(super::Node::Code(absent_core, place))
            );
            assert_eq!(
                Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
                walk.atom(super::Node::Held(absent_held))
            );
        }
        domain.truncate_to(before_closures);
        let walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            walk.closure_atom(closure)
        );
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            walk.atom(super::Node::Code(int_zero, place))
        );
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            compare_codes(&core, &domain, ConstantReading::Unread, closure, closure)
        );
    }

    #[test]
    fn stuck_prefixes_distinguish_heads_eliminations_and_refusals()
    {
        let core = CoreArena::new();
        let mut domain = DomainArena::new();
        let floor = domain.watermark();
        let value = domain.value_unit(TermFace::Reduced);
        let neutral = domain
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::from([Elimination::StaticApply(value), Elimination::Force]),
                Unfolding::Unforced(gandr_kernel_term::GlobalIndex::from(0_u32)),
            )
            .expect("a constant can unfold");
        let walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
        assert_eq!(
            Ok(super::Atom::Constant(
                ConstantIndex::from(0_usize),
                super::Rigidity::Flexible
            )),
            walk.stuck(neutral, super::SpinePrefix(0))
        );
        assert_eq!(
            Ok(super::Atom::Applied(
                super::Node::Stuck(neutral, super::SpinePrefix(0)),
                super::Node::Held(value)
            )),
            walk.stuck(neutral, super::SpinePrefix(1))
        );
        assert_eq!(
            Ok(super::Atom::Other(super::Node::Stuck(
                neutral,
                super::SpinePrefix(2)
            ))),
            walk.stuck(neutral, super::SpinePrefix(2))
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            walk.stuck(neutral, super::SpinePrefix(3))
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            walk.stuck(neutral, super::SpinePrefix(usize::MAX))
        );
        domain.truncate_to(floor);
        let walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            walk.stuck(neutral, super::SpinePrefix(0))
        );
    }
    #[test]
    fn native_classifier_endpoints_compare_in_order_and_refuse_a_missing_target()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let integer = core.value_type_base(BaseType::Integer);
        let source = core.value_quote(unit);
        let target = core.value_quote(integer);
        let path = core.value_type_path_universe(source, target);
        let path = core.value_quote(path);
        let reverse = core.value_type_path_universe(target, source);
        let reverse = core.value_quote(reverse);
        let along = core.value_type_path(unit, source, target);
        let along = core.value_quote(along);
        let against = core.value_type_path(unit, target, source);
        let against = core.value_quote(against);
        let mut foreign = core.clone();
        for _ in 0 .. 4_u8 {
            foreign.value_unit();
        }
        let missing = foreign.value_unit();
        let broken = core.value_type_path_universe(source, missing);
        let broken = core.value_quote(broken);
        assert!(core.value(missing).is_none());
        let mut domain = DomainArena::new();
        let left = code_of(&core, &mut domain, path, &[]);
        let right = code_of(&core, &mut domain, path, &[]);
        let reverse = code_of(&core, &mut domain, reverse, &[]);
        let [along_left, along_right, against] =
            [along, along, against].map(|code| code_of(&core, &mut domain, code, &[]));
        let broken = code_of(&core, &mut domain, broken, &[]);
        assert_eq!(
            Ok(CodeComparison::Equal),
            compare_codes(&core, &domain, ConstantReading::Unread, left, right)
        );
        assert_eq!(
            Ok(CodeComparison::Apart),
            compare_codes(&core, &domain, ConstantReading::Unread, left, reverse)
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            compare_codes(&core, &domain, ConstantReading::Unread, left, broken)
        );
        assert_eq!(
            Ok(CodeComparison::Equal),
            compare_codes(
                &core,
                &domain,
                ConstantReading::Unread,
                along_left,
                along_right
            ),
            "a path type compares its carrier and its endpoints"
        );
        assert_eq!(
            Ok(CodeComparison::Apart),
            compare_codes(&core, &domain, ConstantReading::Unread, along_left, against),
            "in order"
        );
        assert_eq!(
            Ok(CodeComparison::Apart),
            compare_codes(&core, &domain, ConstantReading::Unread, along_left, left),
            "and is apart from a universe path"
        );
    }

    #[test]
    fn native_types_compare_identity_labels_and_value_arguments()
    {
        use alloc::collections::BTreeMap;
        use alloc::string::String;

        use gandr_core_term::ConstructorTag;
        use gandr_core_term::FieldLabel;
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let key = FieldLabel::from(String::from("key"));
        let other_key = FieldLabel::from(String::from("other"));
        let record = core.value_record(BTreeMap::from([(key.clone(), first)]));
        let same_record = core.value_record(BTreeMap::from([(key.clone(), second)]));
        let other_record = core.value_record(BTreeMap::from([(other_key.clone(), first)]));
        let name = ConstantIndex::from(0_usize);
        let other_name = ConstantIndex::from(1_usize);
        let indexed = core.value_type_data(name, Vec::from([record]));
        let repeated = core.value_type_data(name, Vec::from([same_record]));
        let renamed = core.value_type_data(other_name, Vec::from([record]));
        let relabeled = core.value_type_data(name, Vec::from([other_record]));
        let constructor_type = core.value_type_data(other_name, Vec::new());
        let constructor = core.value_constructor(
            constructor_type,
            ConstructorTag::from(0_usize),
            Vec::from([first]),
        );
        let other_constructor = core.value_constructor(
            constructor_type,
            ConstructorTag::from(1_usize),
            Vec::from([first]),
        );
        let tagged = core.value_type_data(name, Vec::from([constructor]));
        let retagged = core.value_type_data(name, Vec::from([other_constructor]));
        let unit_type = core.value_type_unit();
        let wide = core.value_type_record(BTreeMap::from([
            (key.clone(), unit_type),
            (other_key, unit_type),
        ]));
        let narrow = core.value_type_record(BTreeMap::from([(key.clone(), unit_type)]));
        let repeated_type = core.value_type_record(BTreeMap::from([(key.clone(), unit_type)]));
        let nested = core.value_type_record(BTreeMap::from([(key, narrow)]));
        let empty = core.value_type_record(BTreeMap::new());
        let mut domain = DomainArena::new();
        let [
            indexed,
            repeated,
            renamed,
            relabeled,
            tagged,
            retagged,
            wide,
            narrow,
            repeated_type,
            nested,
            empty,
        ] = [
            indexed,
            repeated,
            renamed,
            relabeled,
            tagged,
            retagged,
            wide,
            narrow,
            repeated_type,
            nested,
            empty,
        ]
        .map(|ty| {
            let quote = core.value_quote(ty);
            code_of(&core, &mut domain, quote, &[])
        });
        assert_eq!(
            compare_rigidly(&core, &domain, indexed, repeated),
            CodeComparison::Equal
        );
        assert_eq!(
            compare_rigidly(&core, &domain, indexed, renamed),
            CodeComparison::Apart
        );
        assert_eq!(
            compare_rigidly(&core, &domain, indexed, relabeled),
            CodeComparison::Apart
        );
        assert_eq!(
            compare_rigidly(&core, &domain, tagged, retagged),
            CodeComparison::Apart
        );
        assert_eq!(
            compare_rigidly(&core, &domain, narrow, repeated_type),
            CodeComparison::Equal
        );
        assert_eq!(
            compare_rigidly(&core, &domain, wide, narrow),
            CodeComparison::Apart,
            "width assignment is not definitional equality"
        );
        assert_eq!(
            compare_rigidly(&core, &domain, narrow, nested),
            CodeComparison::Apart
        );
        assert_eq!(
            compare_rigidly(&core, &domain, narrow, empty),
            CodeComparison::Apart
        );
    }
}
