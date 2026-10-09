//! Circuit rules: 2-cells whose boundary pair is derived from a wiring.
//!
//! Instead of writing an `lhs ==> rhs` pair, a circuit rule derives both
//! boundaries from its body. The body is a list of port-named applications,
//! each binding one output port: a frame applies a declared constructor or
//! operation ([`CircuitFrame`]), a redex applies a rewrite ([`CircuitRedex`]).
//! The diagram's two boundaries are read off that wiring by one substitution
//! each — the source boundary replaces every redex by its source, the target
//! boundary replaces every redex by its target — so the rewrite is the
//! diagram and no second body is written.
//!
//! # The derived pair is checked, never synthesized into a sphere
//!
//! The declaration fixes the sphere: at dimension 2 a rule lives at
//! `⋆ ▸ lhs ⇴ rhs` over its sort, and [`CircuitRule::sphere`] is that declared
//! boundary pair. [`derive_boundaries`] computes the wiring's pair; the
//! declaration table ([`check_desc`]) compares the two. Nothing here infers a
//! sphere from a filler, which is what keeps globularity judgmental and makes
//! a mis-glued boundary a failure at the declaration table rather than
//! downstream.
//!
//! # What the resolution does with a port
//!
//! Resolution unfolds the declared output port through the node that binds
//! it:
//!
//! * a port no node binds is an interface port, and stays a boundary variable —
//!   this is how `x` and `y` survive into `add(x, y)`;
//! * a port a frame binds unfolds to that frame's application;
//! * a port a redex binds unfolds to the redex's source or target boundary,
//!   according to the reading;
//! * a port a redex binds to itself is the opaque endpoint a rewrite-sorted
//!   port carries — the wire is the target — so it is a leaf, not a cycle.
//!
//! Any other way a port reaches itself is a wiring cycle, and
//! [`CircuitDerivationError::CyclicWiring`] refuses it: no boundary term
//! unfolds from a cycle.
//!
//! # Scope
//!
//! One declared output port per body, because the derived boundaries land on
//! a term-shaped store, which is single-rooted; a many-out interface is a
//! cell-alphabet question, not a case this derivation quietly admits.
//!
//! [`check_desc`]: crate::check_desc

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use crate::boundary::CircuitNodeBudget;
use crate::code::Name;
use crate::elaborate::RewritePort;
use crate::rule::FreeTerm;
use crate::rule::RuleFace;
use crate::rule::TermNode;
use crate::rule::TermView;

/// Which alphabet a frame's head is declared in: the member kind the ruled
/// block form reads the frame's arrow off.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum FrameHead
{
    /// A constructor head (a `data` member): the frame builds a constructor
    /// application.
    Ctor(Name),
    /// An operation head (an `oper` member): the frame builds an operation
    /// application.
    Op(Name),
}

impl FrameHead
{
    /// The head's declared name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> &Name
    {
        match *self {
            | Self::Ctor(ref name) | Self::Op(ref name) => name,
        }
    }

    /// The application of this head to `args`, in the head's alphabet.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn apply<A>(
        &self,
        args: A,
    ) -> FreeTerm
    where
        A: IntoIterator<Item = FreeTerm>,
    {
        match *self {
            | Self::Ctor(ref name) => FreeTerm::ctor(name.clone(), args),
            | Self::Op(ref name) => FreeTerm::op(name.clone(), args),
        }
    }
}

/// A frame line: a declared constructor or operation applied to its input
/// wiring, binding one output port (`node : add(x′, y′) --> (z)`).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitFrame
{
    /// The applied head and the alphabet it is declared in.
    pub head: FrameHead,
    /// The head's arguments in argument order: input ports as variables, or
    /// ground terms.
    pub args: Box<[FreeTerm]>,
    /// The output port this frame binds.
    pub out: Name,
}

impl CircuitFrame
{
    /// A frame applying `head` to `args` and binding `out`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<A, N>(
        head: FrameHead,
        args: A,
        out: N,
    ) -> Self
    where
        A: Into<Box<[FreeTerm]>>,
        N: Into<Name>,
    {
        Self {
            head,
            args: args.into(),
            out: out.into(),
        }
    }
}

/// A redex line: a rewrite applied to its input wiring, binding one output
/// port (`node : p(x) ==> (x′)`).
///
/// `source` and `target` are the applied rewrite's own boundary pair at this
/// application, the interface pair a rewrite-sorted port carries. An opaque
/// target (the unpinned port form `rule p : Nat ==> Nat`, whose target no term
/// names) is written as the output port itself.
///
/// Both are terms over the body's ports, not leaves: their variable leaves
/// resolve through the wiring like any other port occurrence.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitRedex
{
    /// The applied rewrite's name.
    pub rewrite: Name,
    /// The applied rewrite's source boundary at this application.
    pub source: FreeTerm,
    /// The applied rewrite's target boundary at this application.
    pub target: FreeTerm,
    /// The output port this redex binds.
    pub out: Name,
}

impl CircuitRedex
{
    /// A redex applying `rewrite` between `source` and `target`, binding
    /// `out`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<R, N>(
        rewrite: R,
        source: FreeTerm,
        target: FreeTerm,
        out: N,
    ) -> Self
    where
        R: Into<Name>,
        N: Into<Name>,
    {
        Self {
            rewrite: rewrite.into(),
            source,
            target,
            out: out.into(),
        }
    }
}

/// One body statement of a circuit rule: the two node kinds a body holds.
///
/// A body whose nodes are all [`CircuitNode::Frame`] is a 1-cell definition;
/// a body containing a [`CircuitNode::Redex`] is the 2-cell this module
/// derives boundaries for.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CircuitNode
{
    /// A frame line: the context a rewrite happens inside.
    Frame(CircuitFrame),
    /// A redex line: a rewrite fired at a position.
    Redex(CircuitRedex),
}

impl CircuitNode
{
    /// The output port this node binds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn out(&self) -> &Name
    {
        match *self {
            | Self::Frame(ref frame) => &frame.out,
            | Self::Redex(ref redex) => &redex.out,
        }
    }
}

/// A circuit rule's body: its wiring, plus the interface port the diagram's
/// result leaves by.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitBody
{
    /// The body statements, in source order.
    pub nodes: Box<[CircuitNode]>,
    /// The declared output port the boundary terms are read from.
    pub out: Name,
}

impl CircuitBody
{
    /// A body over `nodes` whose declared output port is `out`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<S, N>(
        nodes: S,
        out: N,
    ) -> Self
    where
        S: Into<Box<[CircuitNode]>>,
        N: Into<Name>,
    {
        Self {
            nodes: nodes.into(),
            out: out.into(),
        }
    }

    /// The node binding each port: the first in source order.
    ///
    /// # Specification
    /// - ensures: one entry per bound port; a port bound by two nodes maps to
    ///   the first, because binding a port twice is a port-linearity failure
    ///   the surface refuses and this order keeps the derivation total rather
    ///   than inventing a second producer.
    /// - panics: none.
    fn producers(&self) -> BTreeMap<&Name, &CircuitNode>
    {
        let mut producers: BTreeMap<&Name, &CircuitNode> = BTreeMap::new();
        for node in &self.nodes {
            producers.entry(node.out()).or_insert(node);
        }
        producers
    }
}

/// A circuit rule member: the sphere its declaration fixes, and the wiring
/// that must derive it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitRule
{
    /// The rule member's name.
    pub name: Name,
    /// The declared sphere: the boundary pair the member's declaration fixes,
    /// carried at dimension 2 as the face's `lhs ⇴ rhs`.
    pub sphere: RuleFace,
    /// The rewrite-sorted ports of the rule's parameter telescope: the binders
    /// a redex line applies by name ([`RewritePort`]).
    ///
    /// An empty telescope means the rule's redex heads are not declared here;
    /// the declaration table checks a redex head against this list only when
    /// it is non-empty ([`check_desc`]).
    ///
    /// [`check_desc`]: crate::check_desc
    pub ports: Box<[RewritePort]>,
    /// The block body whose wiring must derive that pair.
    pub body: CircuitBody,
}

impl CircuitRule
{
    /// A circuit rule named `name`, declared at `sphere`, filled by `body`.
    ///
    /// The parameter telescope defaults to empty and is supplied by
    /// [`Self::with_ports`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        name: N,
        sphere: RuleFace,
        body: CircuitBody,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            name: name.into(),
            sphere,
            ports: Box::default(),
            body,
        }
    }

    /// The same rule carrying `ports` as its parameter telescope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_ports<P>(
        self,
        ports: P,
    ) -> Self
    where
        P: Into<Box<[RewritePort]>>,
    {
        Self {
            ports: ports.into(),
            ..self
        }
    }
}

/// Which of a redex's two boundaries a reading replaces the redex by.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BoundaryReading
{
    /// Replace every redex by its source: the diagram's source boundary.
    Source,
    /// Replace every redex by its target: the diagram's target boundary.
    Target,
}

impl BoundaryReading
{
    /// The redex boundary this reading selects.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    const fn select(
        self,
        redex: &CircuitRedex,
    ) -> &FreeTerm
    {
        match self {
            | Self::Source => &redex.source,
            | Self::Target => &redex.target,
        }
    }
}

/// The boundary pair a wiring derives: the candidate for the declared
/// sphere's two endpoints.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DerivedBoundaries
{
    /// The diagram with every redex replaced by its source.
    pub source: FreeTerm,
    /// The diagram with every redex replaced by its target.
    pub target: FreeTerm,
}

/// Why a wiring derives no boundary term.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CircuitDerivationError
{
    /// The named port is reachable from itself through the wiring, so
    /// unfolding it does not terminate in a term. A redex port bound to itself
    /// is not this case: that is the opaque endpoint, and it is a leaf.
    CyclicWiring(Name),
    /// The unfolding reached the derivation's node ceiling, so the boundary is
    /// declined rather than built.
    ///
    /// A wire consumed twice is unfolded twice, so a body of `n` doubling
    /// frames derives a term of `2ⁿ` nodes. That is the term-shaped store's
    /// own cost; the ceiling is what makes a source-supplied body's blow-up a
    /// defined decline carrying the ceiling it hit, rather than a hang.
    NodeBudget
    {
        /// The ceiling the unfolding reached.
        budget: CircuitNodeBudget,
    },
}

/// Derive both boundaries of a circuit rule's wiring.
///
/// # Specification
/// - ensures: the source boundary is the diagram with every redex replaced by
///   its source, and the target boundary the same diagram with every redex
///   replaced by its target; ports no node binds stay boundary variables.
/// - provides: the pair the declaration table checks against the declared
///   sphere ([`check_desc`]).
/// - fails: [`CircuitDerivationError::CyclicWiring`] when either reading
///   reaches a port from itself; [`CircuitDerivationError::NodeBudget`] when
///   either reading passes [`CircuitNodeBudget::DEFAULT`].
/// - panics: none.
///
/// # Errors
/// Returns [`CircuitDerivationError::CyclicWiring`] naming the port a reading
/// reaches from itself, or [`CircuitDerivationError::NodeBudget`] when a
/// reading passes the standing ceiling.
///
/// # Adequacy
/// - hypothesis: L3 — the congruence body (two disjoint redexes whiskered into
///   one frame) pins both readings at once, because its source and target
///   differ exactly in the redex substitution; a pinned redex target pins that
///   the substitution is a term, not a rename; a two-node cycle pins the
///   refusal.
/// - witness: `circuit::tests::the_congruence_wiring_derives_its_boundary_pair`
/// - witness: `circuit::tests::a_pinned_redex_target_substitutes_into_the_frame`
/// - witness: `circuit::tests::a_wiring_that_closes_a_cycle_derives_nothing`
///
/// [`check_desc`]: crate::check_desc
#[inline]
pub fn derive_boundaries(body: &CircuitBody) -> Result<DerivedBoundaries, CircuitDerivationError>
{
    derive_boundaries_within(body, CircuitNodeBudget::DEFAULT)
}

/// Derive both boundaries under an explicit node ceiling.
///
/// [`derive_boundaries`] is this at [`CircuitNodeBudget::DEFAULT`]. The
/// ceiling is per reading rather than shared between the two, so the two
/// readings of one body are bounded alike and neither can spend the other's
/// allowance.
///
/// # Specification
/// - ensures: as [`derive_boundaries`], within `budget` nodes per reading.
/// - fails: as [`derive_boundaries`], with
///   [`CircuitDerivationError::NodeBudget`] carrying `budget`.
/// - panics: none.
///
/// # Errors
/// See the `- fails:` clause above.
///
/// # Adequacy
/// - hypothesis: L3 — a doubling body declines under the standing ceiling and a
///   body under it derives both readings.
/// - witness: `circuit::tests::a_doubling_body_declines_on_the_node_budget`
/// - witness: `circuit::tests::a_body_within_the_node_budget_still_derives`
#[inline]
pub fn derive_boundaries_within(
    body: &CircuitBody,
    budget: CircuitNodeBudget,
) -> Result<DerivedBoundaries, CircuitDerivationError>
{
    let source = derive_boundary_within(body, BoundaryReading::Source, budget)?;
    let target = derive_boundary_within(body, BoundaryReading::Target, budget)?;
    Ok(DerivedBoundaries { source, target })
}

/// Derive one boundary of a circuit rule's wiring, under the given reading.
///
/// # Specification
/// - ensures: the declared output port is unfolded through the nodes that bind
///   the ports it reaches, with every redex replaced by the boundary `reading`
///   selects and that boundary's own variable leaves resolved in turn; a port
///   no node binds, and a port a redex binds to itself under this reading, are
///   boundary variables.
/// - provides: one endpoint candidate for the declared sphere.
/// - fails: [`CircuitDerivationError::CyclicWiring`] when a port is reachable
///   from itself other than as a redex's own opaque endpoint;
///   [`CircuitDerivationError::NodeBudget`] past
///   [`CircuitNodeBudget::DEFAULT`].
/// - panics: none.
/// - intension: a port bound by two nodes resolves through the first node that
///   binds it, in source order.
///
/// # Errors
/// Returns [`CircuitDerivationError::CyclicWiring`] naming the port this
/// reading reaches from itself, or [`CircuitDerivationError::NodeBudget`]
/// when the reading passes the standing ceiling.
///
/// # Adequacy
/// - hypothesis: L3 — the reading is the only decision surface, so the
///   congruence body distinguishes the two arms pointwise (`add(x, y)` against
///   `add(x′, y′)`), and the cycle guard is distinguished by the two-node
///   cycle.
/// - witness: `circuit::tests::the_congruence_wiring_derives_its_boundary_pair`
/// - witness: `circuit::tests::a_redex_boundary_resolves_its_own_port_leaves`
/// - witness: `circuit::tests::an_unbound_port_stays_a_boundary_variable`
/// - witness: `circuit::tests::a_reconvergent_wire_is_unfolded_at_each_consumption`
/// - witness: `circuit::tests::a_wiring_that_closes_a_cycle_derives_nothing`
#[inline]
pub fn derive_boundary(
    body: &CircuitBody,
    reading: BoundaryReading,
) -> Result<FreeTerm, CircuitDerivationError>
{
    derive_boundary_within(body, reading, CircuitNodeBudget::DEFAULT)
}

/// Derive one boundary under an explicit node ceiling.
///
/// [`derive_boundary`] is this at [`CircuitNodeBudget::DEFAULT`]. The
/// ceiling counts the unfolding's node visits — a port resolved, a term node
/// walked, or an application rebuilt — and every node the reading emits is
/// one of those, so the ceiling bounds the derived term's size in the
/// currency the reconvergence blow-up is measured in.
///
/// # Specification
/// - ensures: as [`derive_boundary`], while the reading visits at most `budget`
///   nodes.
/// - fails: as [`derive_boundary`], with [`CircuitDerivationError::NodeBudget`]
///   carrying `budget` once the reading visits one node past it.
/// - panics: none.
/// - intension: an explicit worklist; the ports on the active unfolding path
///   are a set, so a port met again while its own subtree is open is a cycle,
///   and a port met again after its subtree closed is reconvergence.
///
/// # Errors
/// See the `- fails:` clause above.
///
/// # Adequacy
/// - hypothesis: L1 evidence — one ceiling, so a body that stays under it and a
///   body of doubling frames that passes it separate the predicate.
/// - witness: `circuit::tests::a_doubling_body_declines_on_the_node_budget`
/// - witness: `circuit::tests::a_body_within_the_node_budget_still_derives`
/// - witness: `circuit::tests::the_node_budget_is_per_reading_and_explicit_when_a_caller_wants_one`
#[inline]
pub fn derive_boundary_within(
    body: &CircuitBody,
    reading: BoundaryReading,
    budget: CircuitNodeBudget,
) -> Result<FreeTerm, CircuitDerivationError>
{
    /// One step of the unfolding worklist.
    enum Step<'body>
    {
        /// Resolve a port through the node that binds it.
        Port(&'body Name),
        /// Unfold a term, resolving its port leaves.
        Term(TermNode<'body>),
        /// Rebuild a frame's application over the last results.
        Finish(&'body FrameHead, usize),
        /// Rebuild a constructor application over the last results.
        FinishCtor(&'body Name, usize),
        /// Rebuild an operation application over the last results.
        FinishOp(&'body Name, usize),
        /// The port's subtree is built: take it off the active path.
        Leave(&'body Name),
    }

    let producers = body.producers();
    let ceiling = usize::from(budget);
    let mut emitted: usize = 0;
    let mut path: BTreeSet<&Name> = BTreeSet::new();
    let mut results: Vec<FreeTerm> = Vec::new();
    let mut stack: Vec<Step<'_>> = vec![Step::Port(&body.out)];
    while let Some(step) = stack.pop() {
        // Charge one node visit per resolution, term node, or rebuild. Every
        // node the reading emits is charged, so the count bounds the derived
        // term's size; the `Leave` bookkeeping step is not a visit.
        if !matches!(step, Step::Leave(_)) {
            emitted = emitted.saturating_add(1);
            if emitted > ceiling {
                return Err(CircuitDerivationError::NodeBudget { budget });
            }
        }
        match step {
            | Step::Port(port) => {
                let Some(node) = producers.get(port).copied()
                else {
                    // An interface port: no node binds it, so it is a
                    // boundary variable.
                    results.push(FreeTerm::var(port.clone()));
                    continue;
                };
                match *node {
                    | CircuitNode::Redex(ref redex) => {
                        let bound = reading.select(redex);
                        if matches!(bound.view(), TermView::Var(name) if name == port) {
                            // The opaque endpoint a rewrite-sorted port
                            // carries: the wire is the boundary term.
                            results.push(FreeTerm::var(port.clone()));
                            continue;
                        }
                        if !path.insert(port) {
                            return Err(CircuitDerivationError::CyclicWiring(port.clone()));
                        }
                        stack.push(Step::Leave(port));
                        stack.push(Step::Term(bound.to_node()));
                    },
                    | CircuitNode::Frame(ref frame) => {
                        if !path.insert(port) {
                            return Err(CircuitDerivationError::CyclicWiring(port.clone()));
                        }
                        stack.push(Step::Leave(port));
                        stack.push(Step::Finish(&frame.head, frame.args.len()));
                        stack.extend(frame.args.iter().rev().map(|arg| Step::Term(arg.to_node())));
                    },
                }
            },
            | Step::Term(term) => match term.view() {
                | TermView::Var(name) => stack.push(Step::Port(name)),
                | TermView::Ctor { name, args } => {
                    stack.push(Step::FinishCtor(name, args.len()));
                    let args: Vec<TermNode<'_>> = args.collect();
                    stack.extend(args.iter().rev().copied().map(Step::Term));
                },
                | TermView::Op { name, args } => {
                    stack.push(Step::FinishOp(name, args.len()));
                    let args: Vec<TermNode<'_>> = args.collect();
                    stack.extend(args.iter().rev().copied().map(Step::Term));
                },
            },
            | Step::Finish(head, arity) => {
                let args = results.split_off(results.len().saturating_sub(arity));
                results.push(head.apply(args));
            },
            | Step::FinishCtor(name, arity) => {
                let args = results.split_off(results.len().saturating_sub(arity));
                results.push(FreeTerm::ctor(name.clone(), args));
            },
            | Step::FinishOp(name, arity) => {
                let args = results.split_off(results.len().saturating_sub(arity));
                results.push(FreeTerm::op(name.clone(), args));
            },
            | Step::Leave(port) => {
                path.remove(port);
            },
        }
    }
    // An empty wiring already resolves its declared output port as an unbound
    // one, so a result is always left; the fallback names the same variable.
    Ok(results
        .pop()
        .unwrap_or_else(|| FreeTerm::var(body.out.clone())))
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::ToString as _;

    use super::*;
    use crate::desc::SurfaceSpan;

    /// The `cong2` body of the ruled block form: two disjoint redexes
    /// whiskered into one `add` frame.
    ///
    /// ```text
    /// rule cong2 : (rule p : Nat ==> Nat, rule q : Nat ==> Nat,
    ///               data x : Nat, data y : Nat) ==> (z : Nat) {
    ///   node : p(x) ==> (x′);
    ///   node : q(y) ==> (y′);
    ///   node : add(x′, y′) --> (z);
    /// }
    /// ```
    ///
    /// # Specification
    /// trivial.
    fn cong2_body() -> CircuitBody
    {
        CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("x\u{2032}"),
                    "x\u{2032}",
                )),
                CircuitNode::Redex(CircuitRedex::new(
                    "q",
                    FreeTerm::var("y"),
                    FreeTerm::var("y\u{2032}"),
                    "y\u{2032}",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("x\u{2032}"), FreeTerm::var("y\u{2032}")],
                    "z",
                )),
            ],
            "z",
        )
    }

    #[test]
    fn the_congruence_wiring_derives_its_boundary_pair()
    {
        let derived = derive_boundaries(&cong2_body()).expect("the wiring is acyclic");
        assert_eq!(
            FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("y")]),
            derived.source,
            "the source replaces each redex by its source"
        );
        assert_eq!(
            FreeTerm::op("add", [
                FreeTerm::var("x\u{2032}"),
                FreeTerm::var("y\u{2032}")
            ]),
            derived.target,
            "the target replaces each redex by its target"
        );
    }

    #[test]
    fn a_pinned_redex_target_substitutes_into_the_frame()
    {
        // A pinned rewrite `rule p : x ==> Succ(x)` fired at `x`: the target
        // boundary carries the rewrite's own target term, not the wire name.
        let body = CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
                    "x\u{2032}",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("x\u{2032}"), FreeTerm::var("y")],
                    "z",
                )),
            ],
            "z",
        );
        let derived = derive_boundaries(&body).expect("the wiring is acyclic");
        assert_eq!(
            FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("y")]),
            derived.source,
            "the source reading takes the pinned rewrite's source"
        );
        assert_eq!(
            FreeTerm::op("add", [
                FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
                FreeTerm::var("y")
            ]),
            derived.target,
            "the target reading substitutes the pinned rewrite's target term"
        );
    }

    #[test]
    fn a_redex_boundary_resolves_its_own_port_leaves()
    {
        // `p : f(a) ==> h(a)` fired at a port `a` the wiring binds to `g(u)`:
        // the rewrite's boundary terms are not leaves, their variables resolve
        // through the wiring like any other port.
        let body = CircuitBody::new(
            [
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("g".into()),
                    [FreeTerm::var("u")],
                    "a",
                )),
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::op("f", [FreeTerm::var("a")]),
                    FreeTerm::op("h", [FreeTerm::var("a")]),
                    "z",
                )),
            ],
            "z",
        );
        let derived = derive_boundaries(&body).expect("the wiring is acyclic");
        assert_eq!(
            FreeTerm::op("f", [FreeTerm::op("g", [FreeTerm::var("u")])]),
            derived.source,
            "the source boundary's own variable leaf resolves through the wiring"
        );
        assert_eq!(
            FreeTerm::op("h", [FreeTerm::op("g", [FreeTerm::var("u")])]),
            derived.target,
            "and so does the target boundary's"
        );
    }

    #[test]
    fn an_unbound_port_stays_a_boundary_variable()
    {
        // A body binding nothing: the declared output port is an interface
        // port, so both readings are that variable.
        let body = CircuitBody::new(Vec::new(), "z");
        let derived = derive_boundaries(&body).expect("an empty wiring is acyclic");
        assert_eq!(
            FreeTerm::var("z"),
            derived.source,
            "an unbound output port is a boundary variable"
        );
        assert_eq!(derived.source, derived.target, "both readings agree on it");
    }

    #[test]
    fn a_constructor_frame_builds_a_constructor_term()
    {
        let body = CircuitBody::new(
            [CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Ctor("Succ".into()),
                [FreeTerm::var("n")],
                "m",
            ))],
            "m",
        );
        let derived = derive_boundaries(&body).expect("the wiring is acyclic");
        assert_eq!(
            FreeTerm::ctor("Succ", [FreeTerm::var("n")]),
            derived.source,
            "a `data` head builds a constructor application, not an operation"
        );
    }

    #[test]
    fn a_reconvergent_wire_is_unfolded_at_each_consumption()
    {
        // One redex output feeding both arguments of one frame — two paths out
        // of a cell rejoining at another, which is reconvergence rather than a
        // cycle: the shared wire is a shared subterm on the term-shaped store.
        let body = CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
                    "w",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("w"), FreeTerm::var("w")],
                    "z",
                )),
            ],
            "z",
        );
        let derived = derive_boundaries(&body).expect("reconvergence is not a cycle");
        assert_eq!(
            FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("x")]),
            derived.source,
            "the shared wire resolves at both consumptions"
        );
        assert_eq!(
            FreeTerm::op("add", [
                FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
                FreeTerm::ctor("Succ", [FreeTerm::var("x")])
            ]),
            derived.target,
            "and carries the redex's target term to both"
        );
    }

    /// How many doubling frames a generated body stacks.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct DoublingLevels(usize);

    /// A chain of `n` doubling frames: each consumes the wire below it twice,
    /// so the derived boundary has `2ⁿ` leaves.
    ///
    /// # Specification
    /// trivial.
    fn doubling_body(levels: DoublingLevels) -> CircuitBody
    {
        let levels = levels.0;
        let mut nodes = Vec::new();
        for level in 0 .. levels {
            let below = if level == 0 {
                Name::from("x")
            }
            else {
                Name::from(format!("w{}", level.saturating_sub(1)))
            };
            nodes.push(CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("add".into()),
                [FreeTerm::var(below.clone()), FreeTerm::var(below)],
                format!("w{level}"),
            )));
        }
        CircuitBody::new(nodes, format!("w{}", levels.saturating_sub(1)))
    }

    #[test]
    fn a_doubling_body_declines_on_the_node_budget()
    {
        const OVER_BUDGET_LEVELS: DoublingLevels = DoublingLevels(20);
        // Twenty doubling frames derive a term of 2²⁰ leaves; the ceiling
        // turns that into a defined decline naming the ceiling rather than a
        // hang.
        let body = doubling_body(OVER_BUDGET_LEVELS);
        assert_eq!(
            Err(CircuitDerivationError::NodeBudget {
                budget: CircuitNodeBudget::DEFAULT
            }),
            derive_boundaries(&body),
            "the derivation declines rather than unfolding 2²⁰ nodes"
        );
    }

    #[test]
    fn a_body_within_the_node_budget_still_derives()
    {
        // Five doubling frames derive 2⁵ leaves, comfortably under the
        // ceiling, and the ceiling is not a cliff the ruled bodies sit near:
        // the `cong2` block derives five nodes.
        let body = doubling_body(DoublingLevels(5));
        assert!(
            derive_boundaries(&body).is_ok(),
            "a body under the ceiling derives as before"
        );
        assert!(
            derive_boundaries(&cong2_body()).is_ok(),
            "the ruled congruence block is nowhere near the ceiling"
        );
    }

    #[test]
    fn the_node_budget_is_per_reading_and_explicit_when_a_caller_wants_one()
    {
        let body = doubling_body(DoublingLevels(8));
        assert!(
            derive_boundary_within(&body, BoundaryReading::Source, CircuitNodeBudget::from(16))
                .is_err(),
            "a tight ceiling declines the same body"
        );
        assert!(
            derive_boundary_within(&body, BoundaryReading::Source, CircuitNodeBudget::DEFAULT)
                .is_ok(),
            "and the standing ceiling admits it"
        );
    }

    #[test]
    fn a_wiring_that_closes_a_cycle_derives_nothing()
    {
        // `node : f(b) --> (a); node : g(a) --> (b);` — `a` is reachable from
        // itself, and no `feed` statement closes the loop.
        let body = CircuitBody::new(
            [
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("f".into()),
                    [FreeTerm::var("b")],
                    "a",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("g".into()),
                    [FreeTerm::var("a")],
                    "b",
                )),
            ],
            "a",
        );
        assert_eq!(
            Err(CircuitDerivationError::CyclicWiring("a".into())),
            derive_boundary(&body, BoundaryReading::Source),
            "a cycle in the wiring refuses the derivation, naming the port"
        );
    }

    #[test]
    fn the_declared_sphere_is_carried_beside_the_wiring()
    {
        let sphere = RuleFace::new(
            FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("y")]),
            FreeTerm::op("add", [
                FreeTerm::var("x\u{2032}"),
                FreeTerm::var("y\u{2032}"),
            ]),
            Vec::new(),
            SurfaceSpan::new(0.into(), 1.into()),
        );
        let rule = CircuitRule::new("cong2", sphere.clone(), cong2_body());
        assert_eq!(sphere.lhs, rule.sphere.lhs, "the sphere is carried whole");
        assert_eq!(
            "z",
            rule.body.out.to_string(),
            "the body names the interface port its boundaries are read from"
        );
    }

    #[test]
    fn a_node_reports_the_port_it_binds()
    {
        let frame = CircuitNode::Frame(CircuitFrame::new(
            FrameHead::Ctor("Zero".into()),
            Vec::new(),
            "z",
        ));
        assert_eq!(
            "z",
            frame.out().to_string(),
            "a frame binds its output port"
        );
        let redex = CircuitNode::Redex(CircuitRedex::new(
            "p",
            FreeTerm::var("x"),
            FreeTerm::var("x\u{2032}"),
            "x\u{2032}",
        ));
        assert_eq!(
            "x\u{2032}",
            redex.out().to_string(),
            "a redex binds its output port"
        );
        assert_eq!(
            "Zero",
            FrameHead::Ctor("Zero".into()).name().to_string(),
            "a head reports its declared name"
        );
    }
}
