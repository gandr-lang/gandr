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
//! # Many-out interfaces and nodes
//!
//! A body declares one output port per result. One is the term-shaped case;
//! several make it many-rooted, and each root is unfolded on its own into one
//! component of a results tuple ([`FreeTerm::results`]) — the product layer
//! of a multi-output arity, the named result tuple of Spivak, Garner and
//! Fairbanks's bridge diagrams (*Functorial Aggregation*, arXiv:2111.10968).
//! A frame binds one port per output of its head, so a many-out operation is
//! a node like any other. A term holds a many-out application only whole, as
//! the tuple it returns: a many-out frame whose ports are exactly the body's
//! declared outputs, in its own order, derives its application, and reading
//! one of its outputs on its own is the projection the cartesian structure
//! of a Lawvere theory adds to a PROP's linear wirings (Bonchi, Sobociński and
//! Zanasi, *Lawvere categories as composed PROPs*), which the boundary
//! language does not carry: [`CircuitDerivationError::SplitOutputs`] names
//! that port rather than deriving a term that drops the node's other outputs.
//!
//! [`check_desc`]: crate::check_desc
//!
//! # Circuit rules
//!
//! A circuit rule's boundary pair is derived, never written: the source is the
//! wiring with every redex replaced by its source, the target with every redex
//! replaced by its target. The declared sphere stays the declaration's, and
//! `check_desc` compares the derived pair against it, so a mis-glued boundary
//! is refused at the declaration table. Derivation unfolds each port once per
//! consumption, so a reconvergent wire is copied into each reading; the
//! unfolded size is bounded by `CircuitNodeBudget` (default 4,096 nodes per
//! reading), and a wiring that closes a cycle is refused by the port that
//! closes it. `derive_boundaries_within` and `derive_boundary_within` take an
//! explicit budget.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

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
            Self::Ctor(ref name) | Self::Op(ref name) => name,
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
            Self::Ctor(ref name) => FreeTerm::ctor(name.clone(), args),
            Self::Op(ref name) => FreeTerm::op(name.clone(), args),
        }
    }
}

/// A frame line: a declared constructor or operation applied to its input
/// wiring, binding one output port per output of its head (`node : add(x′,
/// y′) --> (z)`, `node : divmod(m, n) --> (q, r)`).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitFrame
{
    /// The applied head and the alphabet it is declared in.
    pub head: FrameHead,
    /// The head's arguments in argument order: input ports as variables, or
    /// ground terms.
    pub args: Box<[FreeTerm]>,
    /// The output ports this frame binds, in the head's output-port order;
    /// more than one makes the frame a many-out node.
    pub outs: Box<[Name]>,
}

impl CircuitFrame
{
    /// A frame applying `head` to `args` and binding the one port `out`.
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
        Self::binding(head, args, [out.into()])
    }

    /// A frame applying `head` to `args` and binding `outs`, one port per
    /// output of the head, in port order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn binding<A, O>(
        head: FrameHead,
        args: A,
        outs: O,
    ) -> Self
    where
        A: Into<Box<[FreeTerm]>>,
        O: Into<Box<[Name]>>,
    {
        Self {
            head,
            args: args.into(),
            outs: outs.into(),
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
    /// The output ports this node binds, in port order: one for a redex line,
    /// one per output of its head for a frame.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn outs(&self) -> &[Name]
    {
        match *self {
            Self::Frame(ref frame) => &frame.outs,
            Self::Redex(ref redex) => core::slice::from_ref(&redex.out),
        }
    }
}

/// A circuit rule's body: its wiring, the interface ports the diagram's
/// results leave by, and the feeds that close its loops.
///
/// One declared output port is the common, term-shaped case. Several make the
/// body many-rooted: each root's boundary is derived on its own and the
/// derived boundary is the results tuple of them, in port order
/// ([`FreeTerm::results`]).
///
/// A feed carries a source wire back, one step later, as a port the nodes
/// read. The nodes and roots are the body's cut-open form: no node binds a fed
/// port, so a boundary reading meets it as a boundary variable, and the feeds
/// close the loop again.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitBody
{
    /// The body statements, in source order.
    pub nodes: Box<[CircuitNode]>,
    /// The declared output ports the boundary terms are read from, in port
    /// order; never empty.
    pub outs: Box<[Name]>,
    /// The feeds, in source order.
    pub feeds: Box<[CircuitFeed]>,
}

/// One feed of a circuit body: the wire it reads and the port it delivers
/// that wire's value to one step later.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CircuitFeed
{
    /// The wire fed back.
    pub source: Name,
    /// The port the nodes read it at.
    pub port: Name,
}

/// How a body's declared output ports are read: one root, a many-out frame
/// whose outputs are exactly those ports, or a tuple of roots each read on
/// its own.
#[derive(Clone, Copy, Debug)]
pub enum Roots<'body>
{
    /// One declared output port.
    One(&'body Name),
    /// The ports a single many-out frame binds, in its own port order: the
    /// frame's application stands for its whole result tuple.
    Whole(&'body CircuitFrame, &'body Name),
    /// Several ports, each unfolded separately into one component of the
    /// results tuple.
    Tuple(&'body [Name]),
}

impl CircuitBody
{
    /// A body over `nodes` whose one declared output port is `out`.
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
        Self::rooted(nodes, [out.into()])
    }

    /// A body over `nodes` whose declared output ports are `outs`, in port
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rooted<S, O>(
        nodes: S,
        outs: O,
    ) -> Self
    where
        S: Into<Box<[CircuitNode]>>,
        O: Into<Box<[Name]>>,
    {
        Self {
            nodes: nodes.into(),
            outs: outs.into(),
            feeds: Box::default(),
        }
    }

    /// This body with `feeds` closing its loops.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_feeds<F>(
        self,
        feeds: F,
    ) -> Self
    where
        F: Into<Box<[CircuitFeed]>>,
    {
        Self {
            feeds: feeds.into(),
            ..self
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct and duplicate bound ports are observed
    ///   through both boundary readings; choosing the later duplicate changes
    ///   its constructor and losing a port leaves an unexpected variable. The
    ///   predicate reads each node and entry once: every entry is a node of
    ///   this body bound to its port, and the producer of each node's port sits
    ///   at or before that node, which for the port's first binder means the
    ///   binder itself.
    /// - witness: `circuit::tests::duplicate_producers_keep_the_first_source_binding`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body inserts every port of every node once; the check reads every port and every entry once"
        )
    )]
    #[spec(ensures: |ref producers| producers.iter().all(|(port, producer)| producer.outs().contains(*port)
            && self.nodes.as_ptr_range().contains(&core::ptr::from_ref(*producer)))
        && self.nodes.iter().all(|node| node.outs().iter().all(|port| producers.get(port)
            .is_some_and(|producer| core::ptr::from_ref(*producer) <= core::ptr::from_ref(node)))))]
    pub(crate) fn producers(&self) -> BTreeMap<&Name, &CircuitNode>
    {
        let mut producers: BTreeMap<&Name, &CircuitNode> = BTreeMap::new();
        for node in &self.nodes {
            for port in node.outs() {
                producers.entry(port).or_insert(node);
            }
        }
        producers
    }

    /// How the declared output ports are read.
    ///
    /// # Specification
    /// - ensures: [`Roots::One`] for one declared port; [`Roots::Whole`] when
    ///   there are several and the first port's producer is a frame binding
    ///   exactly the declared ports in the same order; [`Roots::Tuple`]
    ///   otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one root, a many-out frame's ports as the roots in
    ///   order, the same ports reversed and two independent roots are observed
    ///   as derived boundaries; reading a reversed tuple as whole or a whole
    ///   frame as a tuple changes them.
    /// - witness: `circuit::tests::a_two_rooted_body_derives_one_boundary_per_root`
    /// - witness: `circuit::tests::a_many_out_frame_leaving_whole_is_its_application`
    #[spec(ensures: |ret| match ret {
        Roots::One(port) => self.outs.len() == 1 && self.outs.first() == Some(port),
        Roots::Whole(frame, _) => self.outs.len() > 1 && frame.outs == self.outs,
        Roots::Tuple(ports) => ports.len() != 1
            && core::ptr::eq(core::ptr::from_ref(ports), &raw const *self.outs),
    })]
    pub(crate) fn roots<'body>(
        &'body self,
        producers: &BTreeMap<&Name, &'body CircuitNode>,
    ) -> Roots<'body>
    {
        match *self.outs {
            [ref port] => Roots::One(port),
            [ref first, ..] => match producers.get(first).copied() {
                Some(&CircuitNode::Frame(ref frame)) if frame.outs == self.outs => {
                    Roots::Whole(frame, first)
                },
                Some(_) | None => Roots::Tuple(&self.outs),
            },
            [] => Roots::Tuple(&self.outs),
        }
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
            Self::Source => &redex.source,
            Self::Target => &redex.target,
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
    /// The named port is one output of a many-out node whose outputs do not
    /// leave the body together, in order, as its declared results.
    ///
    /// A boundary is a term, and a term holds a many-out application only
    /// whole: as the result tuple it returns. Reading one output on its own
    /// is a projection, and wiring the outputs apart is copy and discard —
    /// the cartesian structure a Lawvere theory adds to the linear wirings of
    /// a PROP (Bonchi, Sobociński and Zanasi, *Lawvere categories as composed
    /// PROPs*). The boundary language has no projection, so such a port
    /// derives no term rather than one that silently drops the node's other
    /// outputs.
    SplitOutputs(Name),
}

/// Derive both boundaries of a circuit rule's wiring.
///
/// # Specification
/// - ensures: the source boundary is the diagram with every redex replaced by
///   its source, and the target boundary the same diagram with every redex
///   replaced by its target; ports no node binds stay boundary variables; a
///   many-rooted body's boundaries are results tuples, one component per
///   declared output port.
/// - provides: the pair the declaration table checks against the declared
///   sphere ([`check_desc`]).
/// - fails: [`CircuitDerivationError::CyclicWiring`] when either reading
///   reaches a port from itself; [`CircuitDerivationError::SplitOutputs`] when
///   it reaches one output of a many-out node that does not leave whole;
///   [`CircuitDerivationError::NodeBudget`] when either reading passes
///   [`CircuitNodeBudget::DEFAULT`].
/// - panics: none.
///
/// # Errors
/// Returns [`CircuitDerivationError::CyclicWiring`] naming the port a reading
/// reaches from itself, [`CircuitDerivationError::SplitOutputs`] naming the
/// split port, or [`CircuitDerivationError::NodeBudget`] when a reading passes
/// the standing ceiling.
///
/// # Adequacy
/// - hypothesis: L3 — the congruence body (two disjoint redexes whiskered into
///   one frame) pins both readings at once, because its source and target
///   differ exactly in the redex substitution; a pinned redex target pins that
///   the substitution is a term, not a rename; a two-node cycle pins the
///   refusal; a two-rooted body pins the per-root tuple.
/// - witness: `circuit::tests::the_congruence_wiring_derives_its_boundary_pair`
/// - witness: `circuit::tests::a_pinned_redex_target_substitutes_into_the_frame`
/// - witness: `circuit::tests::a_wiring_that_closes_a_cycle_derives_nothing`
/// - witness: `circuit::tests::a_doubling_body_declines_on_the_node_budget`
/// - witness: `circuit::tests::a_two_rooted_body_derives_one_boundary_per_root`
/// - witness: `circuit::tests::one_output_of_a_many_out_node_derives_no_term`
///
/// [`check_desc`]: crate::check_desc
#[inline]
#[spec(ensures: |ref result| match *result {
    | Ok(ref derived) => [&derived.source, &derived.target].into_iter().all(|term|
        term.applied_symbols().count().saturating_add(term.to_node().vars().count()) <= usize::from(CircuitNodeBudget::DEFAULT)),
    | Err(CircuitDerivationError::NodeBudget { budget: observed }) => observed == CircuitNodeBudget::DEFAULT,
    | Err(CircuitDerivationError::CyclicWiring(ref port)) => body.nodes.iter().any(|node| node.outs().contains(port)),
    | Err(CircuitDerivationError::SplitOutputs(ref port)) => body.nodes.iter().any(|node| matches!(*node, CircuitNode::Frame(ref frame) if frame.outs.len() > 1 && frame.outs.contains(port))),
})]
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
/// - hypothesis: L3 — zero, one-short and exact per-reading ceilings on
///   unbound, nullary and unary bodies distinguish off-by-one charging and a
///   shared allowance. Exact terms and budget errors are the observers.
/// - witness: `circuit::tests::a_doubling_body_declines_on_the_node_budget`
/// - witness: `circuit::tests::a_body_within_the_node_budget_still_derives`
/// - witness: `circuit::tests::the_node_budget_is_per_reading_and_explicit_when_a_caller_wants_one`
#[inline]
#[spec(ensures: |ref result| match *result {
    | Ok(ref derived) => [&derived.source, &derived.target].into_iter().all(|term|
        term.applied_symbols().count().saturating_add(term.to_node().vars().count()) <= usize::from(budget)),
    | Err(CircuitDerivationError::NodeBudget { budget: observed }) => observed == budget,
    | Err(CircuitDerivationError::CyclicWiring(ref port)) => body.nodes.iter().any(|node| node.outs().contains(port)),
    | Err(CircuitDerivationError::SplitOutputs(ref port)) => body.nodes.iter().any(|node| matches!(*node, CircuitNode::Frame(ref frame) if frame.outs.len() > 1 && frame.outs.contains(port))),
})]
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
/// - ensures: each declared output port is unfolded through the nodes that bind
///   the ports it reaches, with every redex replaced by the boundary `reading`
///   selects and that boundary's own variable leaves resolved in turn; a port
///   no node binds, and a port a redex binds to itself under this reading, are
///   boundary variables. One declared port is the boundary; the ports of one
///   many-out frame, declared in its own order, are that frame's application;
///   any other several are the results tuple of their unfoldings.
/// - provides: one endpoint candidate for the declared sphere.
/// - fails: [`CircuitDerivationError::CyclicWiring`] when a port is reachable
///   from itself other than as a redex's own opaque endpoint;
///   [`CircuitDerivationError::SplitOutputs`] when a port is one output of a
///   many-out frame read on its own; [`CircuitDerivationError::NodeBudget`]
///   past [`CircuitNodeBudget::DEFAULT`].
/// - panics: none.
/// - intension: a port bound by two nodes resolves through the first node that
///   binds it, in source order.
///
/// # Errors
/// Returns [`CircuitDerivationError::CyclicWiring`] naming the port this
/// reading reaches from itself, [`CircuitDerivationError::SplitOutputs`]
/// naming the split port, or [`CircuitDerivationError::NodeBudget`] when the
/// reading passes the standing ceiling.
///
/// # Adequacy
/// - hypothesis: L3 — both readings of redex/frame bodies, unbound and opaque
///   endpoints, reconvergence, cycles, duplicate producers, two roots and a
///   many-out frame leaving whole or split are observed as exact terms/errors;
///   wrong substitution, source precedence, cycle scope or root order changes
///   one of those observations.
/// - witness: `circuit::tests::the_congruence_wiring_derives_its_boundary_pair`
/// - witness: `circuit::tests::a_redex_boundary_resolves_its_own_port_leaves`
/// - witness: `circuit::tests::an_unbound_port_stays_a_boundary_variable`
/// - witness: `circuit::tests::a_reconvergent_wire_is_unfolded_at_each_consumption`
/// - witness: `circuit::tests::a_wiring_that_closes_a_cycle_derives_nothing`
/// - witness: `circuit::tests::duplicate_producers_keep_the_first_source_binding`
/// - witness: `circuit::tests::a_two_rooted_body_derives_one_boundary_per_root`
/// - witness: `circuit::tests::a_many_out_frame_leaving_whole_is_its_application`
/// - witness: `circuit::tests::one_output_of_a_many_out_node_derives_no_term`
#[inline]
#[spec(ensures: |ref result| match *result {
    | Ok(ref derived) => { let term = derived;
        term.applied_symbols().count().saturating_add(term.to_node().vars().count()) <= usize::from(CircuitNodeBudget::DEFAULT) },
    | Err(CircuitDerivationError::NodeBudget { budget: observed }) => observed == CircuitNodeBudget::DEFAULT,
    | Err(CircuitDerivationError::CyclicWiring(ref port)) => body.nodes.iter().any(|node| node.outs().contains(port)),
    | Err(CircuitDerivationError::SplitOutputs(ref port)) => body.nodes.iter().any(|node| matches!(*node, CircuitNode::Frame(ref frame) if frame.outs.len() > 1 && frame.outs.contains(port))),
})]
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
/// - hypothesis: L3 — zero, one-short and exact ceilings on unbound, nullary
///   and unary bodies have exact terms or budget refusals. Off-by-one charges,
///   counting bookkeeping and sharing the allowance change those results.
/// - witness: `circuit::tests::a_doubling_body_declines_on_the_node_budget`
/// - witness: `circuit::tests::a_body_within_the_node_budget_still_derives`
/// - witness: `circuit::tests::the_node_budget_is_per_reading_and_explicit_when_a_caller_wants_one`
#[inline]
#[spec(ensures: |ref result| match *result {
    | Ok(ref derived) => { let term = derived;
        term.applied_symbols().count().saturating_add(term.to_node().vars().count()) <= usize::from(budget) },
    | Err(CircuitDerivationError::NodeBudget { budget: observed }) => observed == budget,
    | Err(CircuitDerivationError::CyclicWiring(ref port)) => body.nodes.iter().any(|node| node.outs().contains(port)),
    | Err(CircuitDerivationError::SplitOutputs(ref port)) => body.nodes.iter().any(|node| matches!(*node, CircuitNode::Frame(ref frame) if frame.outs.len() > 1 && frame.outs.contains(port))),
})]
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
        /// Unfold a frame's application, entered through `port`.
        Frame(&'body CircuitFrame, &'body Name),
        /// Unfold a term, resolving its port leaves.
        Term(TermNode<'body>),
        /// Rebuild a frame's application over the last results.
        Finish(&'body FrameHead, usize),
        /// Rebuild a constructor application over the last results.
        FinishCtor(&'body Name, usize),
        /// Rebuild an operation application over the last results.
        FinishOp(&'body Name, usize),
        /// Rebuild a results tuple over the last results.
        FinishResults(usize),
        /// The port's subtree is built: take it off the active path.
        Leave(&'body Name),
    }

    let producers = body.producers();
    let ceiling = usize::from(budget);
    let mut emitted: usize = 0;
    let mut path: BTreeSet<&Name> = BTreeSet::new();
    let mut results: Vec<FreeTerm> = Vec::new();
    let mut stack: Vec<Step<'_>> = match body.roots(&producers) {
        Roots::One(port) => vec![Step::Port(port)],
        Roots::Whole(frame, port) => vec![Step::Frame(frame, port)],
        Roots::Tuple(ports) => {
            let mut steps = Vec::with_capacity(ports.len().saturating_add(1));
            steps.push(Step::FinishResults(ports.len()));
            steps.extend(ports.iter().rev().map(Step::Port));
            steps
        },
    };
    let mut pending: Vec<TermNode<'_>> = Vec::new();
    while let Some(step) = stack.pop() {
        // Charge one node visit per resolution, term node, or rebuild. Every
        // node the reading emits is charged, so the count bounds the derived
        // term's size; the `Leave` bookkeeping step is not a visit, and
        // entering a frame is the visit its port's resolution already paid.
        if !matches!(step, Step::Leave(_) | Step::Frame(..)) {
            emitted = emitted.saturating_add(1);
            if emitted > ceiling {
                return Err(CircuitDerivationError::NodeBudget { budget });
            }
        }
        match step {
            Step::Port(port) => {
                let Some(node) = producers.get(port).copied()
                else {
                    // An interface port: no node binds it, so it is a
                    // boundary variable.
                    results.push(FreeTerm::var(port.clone()));
                    continue;
                };
                match *node {
                    CircuitNode::Redex(ref redex) => {
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
                    CircuitNode::Frame(ref frame) if frame.outs.len() > 1 => {
                        return Err(CircuitDerivationError::SplitOutputs(port.clone()));
                    },
                    CircuitNode::Frame(ref frame) => stack.push(Step::Frame(frame, port)),
                }
            },
            Step::Frame(frame, port) => {
                if !path.insert(port) {
                    return Err(CircuitDerivationError::CyclicWiring(port.clone()));
                }
                stack.push(Step::Leave(port));
                stack.push(Step::Finish(&frame.head, frame.args.len()));
                stack.extend(frame.args.iter().rev().map(|arg| Step::Term(arg.to_node())));
            },
            Step::Term(term) => {
                let (finish, args) = match term.view() {
                    TermView::Var(name) => {
                        stack.push(Step::Port(name));
                        continue;
                    },
                    TermView::Ctor { name, args } => (Step::FinishCtor(name, args.len()), args),
                    TermView::Op { name, args } => (Step::FinishOp(name, args.len()), args),
                    TermView::Results { args } => (Step::FinishResults(args.len()), args),
                };
                stack.push(finish);
                pending.clear();
                pending.extend(args);
                stack.extend(pending.iter().rev().copied().map(Step::Term));
            },
            Step::Finish(head, arity) => {
                let args = results.split_off(results.len().saturating_sub(arity));
                results.push(head.apply(args));
            },
            Step::FinishCtor(name, arity) => {
                let args = results.split_off(results.len().saturating_sub(arity));
                results.push(FreeTerm::ctor(name.clone(), args));
            },
            Step::FinishOp(name, arity) => {
                let args = results.split_off(results.len().saturating_sub(arity));
                results.push(FreeTerm::op(name.clone(), args));
            },
            Step::FinishResults(arity) => {
                let components = results.split_off(results.len().saturating_sub(arity));
                results.push(FreeTerm::results(components));
            },
            Step::Leave(port) => {
                path.remove(port);
            },
        }
    }
    // Every root reading leaves exactly one result; the fallback names the
    // first declared port, which is how an empty wiring resolves it.
    Ok(results.pop().unwrap_or_else(|| {
        body.outs
            .first()
            .map_or_else(|| FreeTerm::results([]), |port| FreeTerm::var(port.clone()))
    }))
}

#[cfg(test)]
mod tests
{
    use alloc::format;

    use super::*;

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

    /// `divmod(m′, n)` as one frame binding `(q, r)`.
    ///
    /// # Specification
    /// trivial.
    fn divmod_frame() -> CircuitNode
    {
        CircuitNode::Frame(CircuitFrame::binding(
            FrameHead::Op("divmod".into()),
            [FreeTerm::var("m\u{2032}"), FreeTerm::var("n")],
            ["q", "r"].map(Name::from),
        ))
    }

    #[test]
    fn a_two_rooted_body_derives_one_boundary_per_root()
    {
        // `node : p(x) ==> (x′); node : f(y) --> (b);` read out at `(x′, b)`:
        // each root unfolds on its own, in declared order, and the redex
        // rewrites only the first component.
        let nodes = [
            CircuitNode::Redex(CircuitRedex::new(
                "p",
                FreeTerm::var("x"),
                FreeTerm::var("x\u{2032}"),
                "x\u{2032}",
            )),
            CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("f".into()),
                [FreeTerm::var("y")],
                "b",
            )),
        ];
        let fy = || FreeTerm::op("f", [FreeTerm::var("y")]);
        for (outs, source, target) in [
            (
                ["x\u{2032}", "b"],
                FreeTerm::results([FreeTerm::var("x"), fy()]),
                FreeTerm::results([FreeTerm::var("x\u{2032}"), fy()]),
            ),
            (
                ["b", "x\u{2032}"],
                FreeTerm::results([fy(), FreeTerm::var("x")]),
                FreeTerm::results([fy(), FreeTerm::var("x\u{2032}")]),
            ),
        ] {
            let body = CircuitBody::rooted(nodes.clone(), outs.map(Name::from));
            let derived = derive_boundaries(&body).expect("the wiring is acyclic");
            assert_eq!(
                (source, target),
                (derived.source, derived.target),
                "the roots read out in declared order"
            );
        }
    }

    #[test]
    fn a_many_out_frame_leaving_whole_is_its_application()
    {
        // `node : p(m) ==> (m′); node : divmod(m′, n) --> (q, r);` read out at
        // `(q, r)`: the frame's ports leave together, in its order, so the
        // boundary is the application standing for its result tuple.
        let redex = CircuitNode::Redex(CircuitRedex::new(
            "p",
            FreeTerm::var("m"),
            FreeTerm::var("m\u{2032}"),
            "m\u{2032}",
        ));
        let body = CircuitBody::rooted([redex, divmod_frame()], ["q", "r"].map(Name::from));
        let derived = derive_boundaries(&body).expect("the wiring is acyclic");
        assert_eq!(
            FreeTerm::op("divmod", [FreeTerm::var("m"), FreeTerm::var("n")]),
            derived.source
        );
        assert_eq!(
            FreeTerm::op("divmod", [FreeTerm::var("m\u{2032}"), FreeTerm::var("n")]),
            derived.target
        );
    }

    #[test]
    fn one_output_of_a_many_out_node_derives_no_term()
    {
        // Read out reversed, alone, or beside another root, a port of the
        // frame is one projection of its tuple, which no term carries.
        let other = CircuitNode::Frame(CircuitFrame::new(FrameHead::Op("f".into()), [], "z"));
        for (outs, split) in [
            (&["r", "q"][..], "r"),
            (&["q"][..], "q"),
            (&["z", "r"][..], "r"),
        ] {
            let body = CircuitBody::rooted(
                [divmod_frame(), other.clone()],
                outs.iter().copied().map(Name::from).collect::<Vec<_>>(),
            );
            assert_eq!(
                Err(CircuitDerivationError::SplitOutputs(Name::from(split))),
                derive_boundaries(&body),
                "reading {outs:?}"
            );
        }
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
    /// - ensures: one ordered doubling frame per requested level; every frame
    ///   has two arguments and the body names the final level's output.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a five-level body derives the exact repeated binary
    ///   term, while twenty levels exceed the ceiling; dropped frames, wrong
    ///   predecessor links and changed arity alter that term or its refusal.
    /// - witness: `circuit::tests::a_body_within_the_node_budget_still_derives`
    /// - witness: `circuit::tests::a_doubling_body_declines_on_the_node_budget`
    #[spec(ensures: |ref body| body.nodes.len() == levels.0
        && body.nodes.iter().all(|node| matches!(*node, CircuitNode::Frame(ref frame) if frame.args.len() == 2)))]
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
        let body = doubling_body(DoublingLevels(5));
        let mut expected = FreeTerm::var("x");
        for _ in 0 .. 5_usize {
            expected = FreeTerm::op("add", [expected.clone(), expected]);
        }
        assert_eq!(
            derive_boundaries(&body),
            Ok(DerivedBoundaries {
                source: expected.clone(),
                target: expected
            })
        );
    }

    #[test]
    fn the_node_budget_is_per_reading_and_explicit_when_a_caller_wants_one()
    {
        for (body, exact, expected) in [
            (CircuitBody::new([], "x"), 1_usize, FreeTerm::var("x")),
            (
                CircuitBody::new(
                    [CircuitNode::Frame(CircuitFrame::new(
                        FrameHead::Ctor("Zero".into()),
                        [],
                        "z",
                    ))],
                    "z",
                ),
                2,
                FreeTerm::ctor("Zero", []),
            ),
            (
                CircuitBody::new(
                    [CircuitNode::Frame(CircuitFrame::new(
                        FrameHead::Op("f".into()),
                        [FreeTerm::var("x")],
                        "z",
                    ))],
                    "z",
                ),
                4,
                FreeTerm::op("f", [FreeTerm::var("x")]),
            ),
        ] {
            let short = CircuitNodeBudget::from(exact.saturating_sub(1));
            let budget = CircuitNodeBudget::from(exact);
            for reading in [BoundaryReading::Source, BoundaryReading::Target] {
                assert_eq!(
                    derive_boundary_within(&body, reading, short),
                    Err(CircuitDerivationError::NodeBudget { budget: short })
                );
                assert_eq!(
                    derive_boundary_within(&body, reading, budget),
                    Ok(expected.clone())
                );
            }
            assert_eq!(
                derive_boundaries_within(&body, short),
                Err(CircuitDerivationError::NodeBudget { budget: short })
            );
            assert_eq!(
                derive_boundaries_within(&body, budget),
                Ok(DerivedBoundaries {
                    source: expected.clone(),
                    target: expected
                })
            );
        }
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
    fn duplicate_producers_keep_the_first_source_binding()
    {
        let body = CircuitBody::new(
            [
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Ctor("First".into()),
                    [],
                    "shared",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Ctor("Later".into()),
                    [],
                    "shared",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("f".into()),
                    [FreeTerm::var("shared"), FreeTerm::var("free")],
                    "out",
                )),
            ],
            "out",
        );
        let expected = FreeTerm::op("f", [FreeTerm::ctor("First", []), FreeTerm::var("free")]);
        for reading in [BoundaryReading::Source, BoundaryReading::Target] {
            assert_eq!(derive_boundary(&body, reading), Ok(expected.clone()));
        }
    }
}
