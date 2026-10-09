//! Elaborating a circuit block into the boundary language.
//!
//! A rewrite-sorted port becomes the interface pair it binds, and the block's
//! redex becomes the whiskered composite it makes inside the block's frames.
//!
//! # A rewrite-sorted port is sorted by the face, and binds an interface pair
//!
//! A port ranging over rewrites is sorted by the 2-cell face at the level's
//! own arrow — `rule p : Nat ==> Nat` — and the sort is the boundary sort,
//! never the boundary terms. Elaborating that binder binds the triple
//! `(a, b, ρ : a ==> b)`: an [`InterfacePair`], the same shape a hole
//! carries, since a hole is its interface pair. The pinned form
//! `rule p : x ==> x′` stays available when the interface should name its
//! endpoints, and then `a` and `b` are the terms the declaration writes
//! ([`PortFace`]).
//!
//! Sorting a rewrite port by a model's path type `Path(Nat, x, x′)` instead
//! would write the interpretation into the syntax and silently make a
//! directed rewrite invertible. Sorting by the face keeps one spelling across
//! the directed family.
//!
//! # Instantiating a port is one match and one binding
//!
//! `node : p(x) ==> (x′)` unifies the source — the port's source pattern
//! variables take the line's input wiring in declaration order, which is what
//! the boundary language's `r(t₁, …, tₙ)` already means — and binds the
//! target: an endpoint the source does not bind is the opaque endpoint the
//! wire itself supplies, so it becomes the line's output port. The result is
//! the [`CircuitRedex`] the boundary derivation already consumes
//! ([`InterfacePair::instantiate`]).
//!
//! # A block elaborates to a whiskered composite
//!
//! A redex applied inside a frame is the boundary language's whiskering
//! `f(t̄, ρ, ū)`, and congruence is the free coherence of parallel
//! composition: every whiskering is a degenerate two-sided congruence with one
//! side. So elaborating a block produces a [`WhiskeredCell`] — a chain of
//! frame applications around one active cell — against the boundaries
//! [`derive_boundaries`] already fixes.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::CircuitNodeBudget;
use crate::boundary::PortArgumentCount;
use crate::boundary::TermPositionIndex;
use crate::circuit::CircuitBody;
use crate::circuit::CircuitDerivationError;
use crate::circuit::CircuitNode;
use crate::circuit::CircuitRedex;
use crate::circuit::DerivedBoundaries;
use crate::circuit::FrameHead;
use crate::circuit::derive_boundaries;
use crate::code::Name;
use crate::rule::FreeTerm;
use crate::rule::TermNode;
use crate::rule::TermView;
use crate::tree::leaf_image;

/// The face a rewrite-sorted port is declared at: what its declaration writes
/// between the two arrowheads.
///
/// The two forms are the ruled spellings: the sorted form writes the boundary
/// sort, the pinned form writes the endpoint terms. Pinning is all-or-nothing,
/// because one arrow cannot carry a sort on one side and a term on the other.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PortFace
{
    /// The sorted form `rule p : Nat ==> Nat`: the boundary sort on both
    /// sides, and no endpoint terms.
    Sorted(Name),
    /// The pinned form `rule p : x ==> x′`: the declaration names its own
    /// endpoints, and binding pinned rewrites in the parameter telescope is
    /// what lets a congruence cell's body shrink to its frame.
    Pinned
    {
        /// The declared source endpoint.
        source: FreeTerm,
        /// The declared target endpoint.
        target: FreeTerm,
    },
}

/// Which endpoint of a sorted port's interface pair a minted variable names.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum InterfaceRole
{
    /// The source endpoint `a` of `ρ : a ==> b`.
    Source,
    /// The target endpoint `b` of `ρ : a ==> b`.
    Target,
}

/// The variable a sorted port's interface pair carries at one endpoint.
///
/// The sorted form writes no endpoint term, so the endpoints are variables
/// the elaboration mints. They are spelled with mathematical angle brackets,
/// which the surface's identifier lexis cannot produce, so a minted endpoint
/// can never be captured by a body port of the same name. They are also
/// transient: [`InterfacePair::instantiate`] substitutes the source endpoint
/// away and replaces the target endpoint by the line's output port, so no
/// minted name reaches a [`CircuitRedex`] or a derived boundary.
///
/// # Specification
/// - ensures: `{port}⟨source⟩` for the source role and `{port}⟨target⟩` for the
///   target role, so the two endpoints of one port are distinct.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the two roles for the same port have exact minted
///   endpoint spellings; a missing delimiter, wrong role or captured port name
///   changes those endpoints and their distinctness.
/// - witness: `elaborate::tests::a_sorted_port_binds_two_distinct_endpoints`
#[spec(ensures: |ref name| name.as_ref().strip_prefix(port.as_ref()) == Some(match role {
    | InterfaceRole::Source => "⟨source⟩",
    | InterfaceRole::Target => "⟨target⟩",
}))]
fn interface_variable(
    port: &Name,
    role: InterfaceRole,
) -> Name
{
    let role = match role {
        | InterfaceRole::Source => "source",
        | InterfaceRole::Target => "target",
    };
    Name::from(format!("{port}\u{27e8}{role}\u{27e9}"))
}

/// A rewrite-sorted port of a circuit rule's parameter telescope: the binder
/// `rule p : Nat ==> Nat`, whose inhabitant is a rewrite.
///
/// A redex line applies this port by name; the port is not a signature
/// symbol, which is why the declaration table checks a redex head against
/// the telescope rather than against the datatype's constructors and
/// operations.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RewritePort
{
    /// The port's name: the head a redex line applies.
    pub name: Name,
    /// The face the port is sorted by.
    pub face: PortFace,
}

impl RewritePort
{
    /// A port in the sorted form `rule name : sort ==> sort`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sorted<N, S>(
        name: N,
        sort: S,
    ) -> Self
    where
        N: Into<Name>,
        S: Into<Name>,
    {
        Self {
            name: name.into(),
            face: PortFace::Sorted(sort.into()),
        }
    }

    /// A port in the pinned form `rule name : source ==> target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pinned<N>(
        name: N,
        source: FreeTerm,
        target: FreeTerm,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            name: name.into(),
            face: PortFace::Pinned { source, target },
        }
    }

    /// The interface pair this port binds: the triple `(a, b, ρ : a ==> b)`.
    ///
    /// # Specification
    /// - ensures: the pinned form's pair is the two terms its declaration
    ///   writes; the sorted form's pair is two distinct minted endpoint
    ///   variables, because the boundary sort names no terms.
    /// - provides: the binding an instantiating redex line matches against.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sorted and pinned ports are observed as exact
    ///   endpoint terms and the rewrite name; conflating endpoints, retaining
    ///   the sort as a term or replacing a pinned endpoint changes the pair.
    /// - witness: `elaborate::tests::a_sorted_port_binds_two_distinct_endpoints`
    /// - witness: `elaborate::tests::a_pinned_port_binds_the_terms_it_writes`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref pair| pair.rewrite == self.name && match self.face {
        | PortFace::Sorted(_) => pair.source != pair.target
            && matches!(pair.source.view(), TermView::Var(_)) && matches!(pair.target.view(), TermView::Var(_)),
        | PortFace::Pinned { ref source, ref target } => &pair.source == source && &pair.target == target,
    })]
    pub fn interface(&self) -> InterfacePair
    {
        match self.face {
            | PortFace::Sorted(_) => InterfacePair::new(
                self.name.clone(),
                FreeTerm::var(interface_variable(&self.name, InterfaceRole::Source)),
                FreeTerm::var(interface_variable(&self.name, InterfaceRole::Target)),
            ),
            | PortFace::Pinned {
                ref source,
                ref target,
            } => InterfacePair::new(self.name.clone(), source.clone(), target.clone()),
        }
    }
}

/// The interface pair a rewrite binds at one place: the triple
/// `(a, b, ρ : a ==> b)`.
///
/// This is the shape a hole carries — a context is an object of `Cᵒᵖ × C`, a
/// pair `(X / Y)` for a hole admitting a process from `X` to `Y` — and it is
/// what a rewrite-sorted port elaborates to ([`RewritePort::interface`]) and
/// what the active cell of a whiskered composite is ([`ActiveCell::Redex`]).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct InterfacePair
{
    /// The rewrite `ρ` the pair is the interface of.
    pub rewrite: Name,
    /// The source endpoint `a`.
    pub source: FreeTerm,
    /// The target endpoint `b`.
    pub target: FreeTerm,
}

impl InterfacePair
{
    /// The pair `(source, target, rewrite : source ==> target)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<R>(
        rewrite: R,
        source: FreeTerm,
        target: FreeTerm,
    ) -> Self
    where
        R: Into<Name>,
    {
        Self {
            rewrite: rewrite.into(),
            source,
            target,
        }
    }

    /// Instantiate this interface pair at a redex line: unify the source
    /// against the line's input wiring, and bind the target to its output
    /// port.
    ///
    /// `node : p(x) ==> (x′)` supplies `args = [x]` and `out = x′`. The
    /// source's pattern variables take the arguments in declaration order —
    /// the boundary language's own reading of `r(t₁, …, tₙ)` — and the
    /// resulting substitution is applied to both endpoints. A target endpoint
    /// the source does not bind is the opaque endpoint: the declaration names
    /// no term for it, so the wire does, and the line's output port becomes
    /// the target.
    ///
    /// # Specification
    /// - ensures: on success the redex's source is this pair's source under the
    ///   substitution binding its distinct source variables to `args` in
    ///   first-occurrence order; its target is this pair's target under that
    ///   same substitution when the source binds every target variable, and
    ///   `out` when the target is a lone variable the source does not bind.
    /// - provides: the [`CircuitRedex`] a body statement holds, so a
    ///   rewrite-sorted port and the boundary derivation meet at one type.
    /// - fails: [`PortInstantiationError::SourceArity`] when the line supplies
    ///   a number of arguments other than the source's distinct variable count;
    ///   [`PortInstantiationError::UnboundTargetEndpoint`] when the target
    ///   names endpoints the source does not bind and is not itself the lone
    ///   opaque endpoint the output port supplies.
    /// - panics: none.
    /// - intension: source variables are bound in first-occurrence,
    ///   left-to-right order, so a repeated source variable consumes one
    ///   argument rather than two and a linear source's arguments read in
    ///   surface order.
    ///
    /// # Errors
    /// See [`PortInstantiationError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two endpoint arms and the two declines are
    ///   separated pointwise: an unpinned pair leaves the target opaque and so
    ///   reaches `out`, a pinned pair whose target the source binds reaches the
    ///   substituted term, a short argument list reaches the arity decline, and
    ///   a target naming an endpoint neither the source nor the wire supplies
    ///   reaches the endpoint decline.
    /// - witness: `elaborate::tests::instantiating_a_port_unifies_the_source_and_binds_the_target`
    /// - witness: `elaborate::tests::instantiating_a_pinned_port_substitutes_into_its_target`
    /// - witness: `elaborate::tests::a_repeated_source_variable_consumes_one_argument`
    /// - witness: `elaborate::tests::an_instantiation_that_does_not_unify_declines`
    /// - witness: `elaborate::tests::a_target_endpoint_no_wire_supplies_declines`
    /// - witness: `elaborate::tests::instantiation_observes_zero_arity_and_first_occurrence_order`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        | Ok(ref redex) => redex.rewrite == self.rewrite,
        | Err(PortInstantiationError::SourceArity { ref rewrite, expected, supplied }) => rewrite == &self.rewrite && expected != supplied,
        | Err(PortInstantiationError::UnboundTargetEndpoint { ref rewrite, ref endpoints }) => rewrite == &self.rewrite && !endpoints.is_empty()
            && endpoints.iter().all(|name| self.target.to_node().vars().any(|target| target == name)
                && !self.source.to_node().vars().any(|source| source == name)),
    })]
    pub fn instantiate<A, N>(
        &self,
        args: A,
        out: N,
    ) -> Result<CircuitRedex, PortInstantiationError>
    where
        A: Into<Box<[FreeTerm]>>,
        N: Into<Name>,
    {
        let args = args.into();
        let out = out.into();
        let vars = distinct_vars(&self.source);
        if vars.len() != args.len() {
            return Err(PortInstantiationError::SourceArity {
                rewrite: self.rewrite.clone(),
                expected: PortArgumentCount::from(vars.len()),
                supplied: PortArgumentCount::from(args.len()),
            });
        }
        let bindings: BTreeMap<Name, FreeTerm> = vars.into_iter().zip(args.into_vec()).collect();
        let source = substitute(&self.source, &bindings);
        let unbound: Vec<Name> = distinct_vars(&self.target)
            .into_iter()
            .filter(|name| !bindings.contains_key(name))
            .collect();
        let target = if unbound.is_empty() {
            substitute(&self.target, &bindings)
        }
        else if matches!(self.target.view(), TermView::Var(_)) {
            // The opaque endpoint: the declaration names no term for the
            // target, so the wire is the target.
            FreeTerm::var(out.clone())
        }
        else {
            return Err(PortInstantiationError::UnboundTargetEndpoint {
                rewrite: self.rewrite.clone(),
                endpoints: unbound.into(),
            });
        };
        Ok(CircuitRedex::new(self.rewrite.clone(), source, target, out))
    }
}

/// Why a redex line does not instantiate the port it applies.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum PortInstantiationError
{
    /// The line's input wiring does not match the port's source interface:
    /// the source has a different number of distinct pattern variables than
    /// the line supplies arguments.
    SourceArity
    {
        /// The applied rewrite.
        rewrite: Name,
        /// The source interface's distinct variable count.
        expected: PortArgumentCount,
        /// The number of arguments the line supplied.
        supplied: PortArgumentCount,
    },
    /// The declared target names endpoints the source does not bind, and the
    /// target is not the lone opaque endpoint the output port supplies — so
    /// there is no wire for those endpoints to come from. One redex line binds
    /// exactly one output port; a many-out node is a cell-alphabet question,
    /// which this route declines rather than omits.
    UnboundTargetEndpoint
    {
        /// The applied rewrite.
        rewrite: Name,
        /// The target endpoints the source does not bind, in first-occurrence
        /// order.
        endpoints: Box<[Name]>,
    },
}

/// One whiskering level `f(t̄, ·, ū)`: a frame application with one active
/// argument slot.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Whisker
{
    /// The frame's head and the alphabet it is declared in.
    pub head: FrameHead,
    /// The unchanged arguments left of the active slot (`t̄`).
    pub before: Box<[FreeTerm]>,
    /// The unchanged arguments right of the active slot (`ū`).
    pub after: Box<[FreeTerm]>,
}

/// The innermost cell of a whiskered composite.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ActiveCell
{
    /// `here(t)`: the identity (empty) rewrite at a term, which is what a body
    /// with no redex occurrence elaborates to.
    Here(FreeTerm),
    /// `r(t̄)`: the applied rewrite, carried as the interface pair it spans
    /// once the wiring has resolved both of its boundary terms.
    Redex(InterfacePair),
}

quenchant_shape::reason_enum! {
    /// Why a whiskered composite has no active position.
    pub mod active_position {
        /// The reason no position is active.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The composite's innermost cell is an identity rewrite, which is
            /// active nowhere.
            Identity,
        }
    }
}

/// A term of the boundary language: the composite a circuit block's wiring
/// makes out of its redex and its frames.
///
/// Three of the language's four constructions are built here. `here(t)` is
/// the identity rewrite, `r(t̄)` the rule instantiation — carried as the
/// [`InterfacePair`] the application sits between, which is `r` together with
/// the two boundary terms its arguments resolve to — and `f(t̄, ρ, ū)` the
/// whiskering. The fourth, `ρ then ρ′`, is what a body with more than one
/// redex occurrence needs, and it is what [`elaborate_body`] declines rather
/// than builds.
///
/// A composite is a chain of whiskering levels, outermost first, around one
/// active cell, held flat: building, comparing and dropping a composite of
/// any depth never recurses.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WhiskeredCell
{
    /// The whiskering levels, outermost first.
    pub whiskers: Box<[Whisker]>,
    /// The innermost cell the levels whisker.
    pub active: ActiveCell,
}

impl WhiskeredCell
{
    /// `here(t)`: the identity rewrite at `term`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn here(term: FreeTerm) -> Self
    {
        Self {
            whiskers: Box::default(),
            active: ActiveCell::Here(term),
        }
    }

    /// `r(t̄)`: the applied rewrite spanning `pair`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn redex(pair: InterfacePair) -> Self
    {
        Self {
            whiskers: Box::default(),
            active: ActiveCell::Redex(pair),
        }
    }

    /// `f(t̄, ρ, ū)`: the composite `inner` applied in one argument position
    /// of `head`, with the unchanged arguments `before` and `after` on either
    /// side.
    ///
    /// # Specification
    /// - ensures: the new level is outermost, ahead of `inner`'s levels.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested redex whiskers and an identity composite are
    ///   observed through exact levels and active positions; appending the new
    ///   level innermost, losing a level or creating activity changes them.
    /// - witness: `elaborate::tests::a_nested_whisker_reports_its_argument_path`
    /// - witness: `elaborate::tests::an_identity_composite_has_no_active_position`
    #[inline]
    #[must_use]
    #[spec(
        captures: [levels = inner.whiskers.len(), was_identity = matches!(inner.active, ActiveCell::Here(_))],
        ensures: |ref cell| cell.whiskers.len() == levels.saturating_add(1)
            && matches!(cell.active, ActiveCell::Here(_)) == was_identity,
    )]
    pub fn whisker<B, U>(
        head: FrameHead,
        before: B,
        inner: Self,
        after: U,
    ) -> Self
    where
        B: Into<Box<[FreeTerm]>>,
        U: Into<Box<[FreeTerm]>>,
    {
        let mut whiskers = Vec::with_capacity(inner.whiskers.len().saturating_add(1));
        whiskers.push(Whisker {
            head,
            before: before.into(),
            after: after.into(),
        });
        whiskers.extend(inner.whiskers);
        Self {
            whiskers: whiskers.into(),
            active: inner.active,
        }
    }

    /// The composite's active position: the path of argument indices from the
    /// root of the derived boundary down to the redex.
    ///
    /// # Specification
    /// - ensures: [`active_position::Absent::Identity`] for a composite whose
    ///   active cell is [`ActiveCell::Here`]; otherwise the argument index of
    ///   each whiskering level, outermost first, so the empty path is a redex
    ///   at the root.
    /// - provides: the position the shift-equivalence guard's incomparability
    ///   conjunct is asked about.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root redex, two nested unequal argument indices and
    ///   a whiskered identity are observed as exact paths or absence; reversing
    ///   levels, using the right-argument count or inventing an active identity
    ///   position changes those results.
    /// - witness: `elaborate::tests::a_nested_whisker_reports_its_argument_path`
    /// - witness: `elaborate::tests::an_identity_composite_has_no_active_position`
    /// - witness: `elaborate::tests::a_redex_at_the_root_needs_no_whisker`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        | Maybe::Absent(_) => matches!(self.active, ActiveCell::Here(_)),
        | Maybe::Present(ref position) => matches!(self.active, ActiveCell::Redex(_))
            && position.iter().copied().map(usize::from).eq(self.whiskers.iter().map(|whisker| whisker.before.len())),
    })]
    pub fn active_position(&self) -> Maybe<Vec<TermPositionIndex>, active_position::Absent>
    {
        match self.active {
            | ActiveCell::Here(_) => Maybe::Absent(active_position::Absent::Identity),
            | ActiveCell::Redex(_) => Maybe::Present(
                self.whiskers
                    .iter()
                    .map(|whisker| TermPositionIndex::from(whisker.before.len()))
                    .collect(),
            ),
        }
    }
}

/// One redex occurrence in a block's derived boundary: the applied rewrite and
/// where the wiring plants it.
///
/// An occurrence is a position in the boundary term, not a body statement: a
/// wire consumed twice is unfolded twice, so one redex line reconverging into
/// two argument slots is two occurrences.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RedexOccurrence
{
    /// The applied rewrite.
    pub rewrite: Name,
    /// The path of argument indices from the boundary's root to this
    /// occurrence.
    pub position: Box<[TermPositionIndex]>,
}

impl RedexOccurrence
{
    /// An occurrence of `rewrite` at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<R, P>(
        rewrite: R,
        position: P,
    ) -> Self
    where
        R: Into<Name>,
        P: Into<Box<[TermPositionIndex]>>,
    {
        Self {
            rewrite: rewrite.into(),
            position: position.into(),
        }
    }
}

/// Why a circuit block elaborates to no composite.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CircuitElaborationError
{
    /// The wiring derives no boundary pair, so there is nothing to whisker
    /// into.
    Derivation(CircuitDerivationError),
    /// The declared output port unfolds to more than one redex occurrence, so
    /// the composite is not a single whiskering.
    ///
    /// The occurrences are carried with their positions, because the position
    /// order is what says which composite is owed. Two occurrences at
    /// incomparable positions are horizontal composition, which is licensed
    /// exactly on disjoint positions where the two readings are shift-equal
    /// and never any earlier or any wider — the earned witness, not this
    /// elaboration, is what grants it, and it is earned where the rule is
    /// applied rather than where it is declared, against the cells its
    /// rewrite-sorted ports are instantiated by ([`redex_occurrences`] is what
    /// carries the two positions there). Two at comparable positions are
    /// sequential composition, which the boundary language spells
    /// `ρ then ρ′`.
    ManyRedexOccurrences
    {
        /// Every occurrence, in the order the source reading reaches them.
        occurrences: Box<[RedexOccurrence]>,
    },
    /// The occurrence walk reached a position the derived boundary does not
    /// address.
    ///
    /// The walk and the derivation are separate traversals of the same
    /// wiring, so a disagreement between them is reported rather than assumed
    /// away.
    PositionOffBoundary
    {
        /// The rewrite whose occurrence could not be located.
        rewrite: Name,
        /// The path that ran off the boundary term.
        position: Box<[TermPositionIndex]>,
    },
}

/// Elaborate a circuit block into the boundary language: the whiskered
/// composite of its redex inside its frames.
///
/// A redex applied inside a frame is the boundary language's whiskering
/// `f(t̄, ρ, ū)`, and congruence is the free coherence of parallel
/// composition — every whiskering is a degenerate two-sided congruence with
/// one side. So a block whose declared output port unfolds through frames to
/// one redex elaborates to that redex wrapped in one [`Whisker`] per
/// enclosing application, and a block with no redex at all elaborates to
/// `here(t)` at the term its frames build.
///
/// # The position structure this composite exposes
///
/// The composite exposes exactly one active position, and it is a path of
/// argument indices. A whiskered composite is a chain of frame applications
/// ending in one redex, so the redex occupies the path obtained by reading
/// each whisker's argument index from the root
/// ([`WhiskeredCell::active_position`]), and that path addresses the redex's
/// source in the derived source boundary and its target in the derived
/// target boundary. It is the only position at which the composite is not an
/// identity. A body whose declared output port unfolds to two or more redex
/// occurrences therefore has no single-position composite here: it is
/// declined by [`CircuitElaborationError::ManyRedexOccurrences`], which
/// carries every occurrence's rewrite name and position path. Two occurrences
/// at incomparable positions are the horizontal composite that is licensed
/// only against an earned shift-equivalence witness; two at comparable
/// positions are sequential composition, spelled `ρ then ρ′`. Reconvergence
/// produces two occurrences of the same redex, so a wire consumed twice is two
/// positions rather than one.
///
/// # Specification
/// - ensures: a body with no redex occurrence elaborates to
///   [`ActiveCell::Here`] at its derived source boundary; a body with exactly
///   one elaborates to that occurrence's [`InterfacePair`] — its source read
///   from the derived source boundary and its target from the derived target
///   boundary — wrapped in one whisker per enclosing application, whose
///   unchanged arguments are that application's other arguments.
/// - provides: the boundary-language composite a circuit rule's filler denotes,
///   against the boundaries the sphere check already fixed.
/// - fails: [`CircuitElaborationError::Derivation`] when the wiring derives no
///   boundary pair; [`CircuitElaborationError::ManyRedexOccurrences`] when the
///   composite would hold more than one redex occurrence;
///   [`CircuitElaborationError::PositionOffBoundary`] when the occurrence walk
///   and the derivation disagree about the boundary's shape.
/// - panics: none.
/// - intension: the occurrence order is the source reading's own left-to-right
///   unfolding of the declared output port, so the declined report reads in
///   diagram order.
///
/// # Errors
/// See [`CircuitElaborationError`].
///
/// # Adequacy
/// - hypothesis: L3 — the three arms are separated pointwise: a frames-only
///   body reaches `here`, the single-redex congruence body reaches a whisker
///   whose unchanged argument is the frame's other operand, and the two-redex
///   `cong2` body reaches the decline with both positions; the nesting
///   direction is pinned by a two-level frame, where an outermost-first and an
///   innermost-first fold differ.
/// - witness: `elaborate::tests::a_single_redex_block_elaborates_to_a_whiskered_cell`
/// - witness: `elaborate::tests::a_redex_under_two_frames_whiskers_outermost_first`
/// - witness: `elaborate::tests::a_redex_at_the_root_needs_no_whisker`
/// - witness: `elaborate::tests::a_body_with_no_redex_is_the_identity_rewrite`
/// - witness: `elaborate::tests::two_disjoint_redexes_decline_with_incomparable_positions`
/// - witness: `elaborate::tests::a_reconvergent_redex_is_two_occurrences_of_one_rewrite`
/// - witness: `elaborate::tests::a_cyclic_wiring_elaborates_to_nothing`
/// - witness: `elaborate::tests::occurrence_walk_distinguishes_opaque_roots_and_budget_refusals`
#[inline]
#[spec(ensures: |ref result| match *result {
    | Ok(ref cell) => match cell.active {
        | ActiveCell::Here(_) => cell.whiskers.is_empty(),
        | ActiveCell::Redex(ref pair) => body.nodes.iter().any(|node| matches!(*node, CircuitNode::Redex(ref redex) if redex.rewrite == pair.rewrite)),
    },
    | Err(CircuitElaborationError::ManyRedexOccurrences { ref occurrences }) => occurrences.len() > 1,
    | Err(CircuitElaborationError::Derivation(CircuitDerivationError::NodeBudget { budget })) => budget == CircuitNodeBudget::DEFAULT,
    | Err(CircuitElaborationError::Derivation(CircuitDerivationError::CyclicWiring(ref port))) => body.nodes.iter().any(|node| node.out() == port),
    | Err(CircuitElaborationError::PositionOffBoundary { ref rewrite, .. }) => body.nodes.iter().any(|node| matches!(*node, CircuitNode::Redex(ref redex) if &redex.rewrite == rewrite)),
})]
pub fn elaborate_body(body: &CircuitBody) -> Result<WhiskeredCell, CircuitElaborationError>
{
    let derived = derive_boundaries(body).map_err(CircuitElaborationError::Derivation)?;
    let mut occurrences = redex_occurrences(body).map_err(CircuitElaborationError::Derivation)?;
    let Some(occurrence) = occurrences.pop()
    else {
        return Ok(WhiskeredCell::here(derived.source));
    };
    if !occurrences.is_empty() {
        occurrences.push(occurrence);
        return Err(CircuitElaborationError::ManyRedexOccurrences {
            occurrences: occurrences.into(),
        });
    }
    whisker_along(&derived, &occurrence)
}

/// The arguments of an application node, left to right, with its head; an
/// error for a variable.
///
/// # Specification
/// - ensures: the head in its alphabet and the arguments in order for an
///   application; the off-boundary error for a variable, which addresses no
///   argument.
/// - fails: `off_boundary()` for a variable.
/// - panics: none of its own; a panic in `off_boundary` propagates.
///
/// # Errors
/// Returns `off_boundary()` when `node` is a variable.
///
/// # Adequacy
/// - hypothesis: L3 — variables, constructor and operation applications,
///   including a nullary head, are observed as exact errors or ordered
///   head/argument records; invoking the refusal callback on success, wrong
///   alphabets or reordered arguments changes an observation.
/// - witness: `elaborate::tests::application_and_whisker_positions_decline_off_boundary`
#[spec(ensures: |ref result| match *result {
    | Ok((ref head, ref args)) => match node.view() {
        | TermView::Ctor { name, args: expected } => matches!(*head, FrameHead::Ctor(ref actual) if actual == name) && args.iter().copied().eq(expected),
        | TermView::Op { name, args: expected } => matches!(*head, FrameHead::Op(ref actual) if actual == name) && args.iter().copied().eq(expected),
        | TermView::Var(_) => false,
    },
    | Err(_) => matches!(node.view(), TermView::Var(_)),
})]
fn application<E, O>(
    node: TermNode<'_>,
    off_boundary: O,
) -> Result<(FrameHead, Vec<TermNode<'_>>), E>
where
    O: FnOnce() -> E,
{
    match node.view() {
        | TermView::Ctor { name, args } => Ok((FrameHead::Ctor(name.clone()), args.collect())),
        | TermView::Op { name, args } => Ok((FrameHead::Op(name.clone()), args.collect())),
        | TermView::Var(_) => Err(off_boundary()),
    }
}

/// Build the whisker chain addressing `occurrence` in the derived boundary
/// pair.
///
/// # Specification
/// - ensures: one [`Whisker`] per application the position descends through,
///   outermost first, around an [`ActiveCell::Redex`] whose pair is the two
///   boundaries' subterms at that position.
/// - fails: [`CircuitElaborationError::PositionOffBoundary`] when either
///   boundary does not address the position.
/// - panics: none.
///
/// # Errors
/// See the `- fails:` clause above.
///
/// # Adequacy
/// - hypothesis: L3 — root and nested valid positions, variable boundaries and
///   first-past argument indices on either endpoint are observed as exact cells
///   or rewrite/path errors; ignoring a target bound, truncating a path or
///   reversing the whisker chain changes them.
/// - witness: `elaborate::tests::application_and_whisker_positions_decline_off_boundary`
/// - witness: `elaborate::tests::a_redex_under_two_frames_whiskers_outermost_first`
/// - witness: `elaborate::tests::a_redex_at_the_root_needs_no_whisker`
#[spec(ensures: |ref result| match *result {
    | Ok(ref cell) => cell.whiskers.len() == occurrence.position.len()
        && cell.whiskers.iter().map(|whisker| whisker.before.len()).eq(occurrence.position.iter().copied().map(usize::from))
        && matches!(cell.active, ActiveCell::Redex(ref pair) if pair.rewrite == occurrence.rewrite),
    | Err(CircuitElaborationError::PositionOffBoundary { ref rewrite, ref position }) => rewrite == &occurrence.rewrite && position == &occurrence.position,
    | Err(_) => false,
})]
fn whisker_along(
    derived: &DerivedBoundaries,
    occurrence: &RedexOccurrence,
) -> Result<WhiskeredCell, CircuitElaborationError>
{
    let off_boundary = || CircuitElaborationError::PositionOffBoundary {
        rewrite: occurrence.rewrite.clone(),
        position: occurrence.position.clone(),
    };
    let mut whiskers: Vec<Whisker> = Vec::with_capacity(occurrence.position.len());
    let mut source = derived.source.to_node();
    let mut target = derived.target.to_node();
    for &step in &occurrence.position {
        let step = usize::from(step);
        let (head, source_args) = application(source, off_boundary)?;
        let Some(&source_child) = source_args.get(step)
        else {
            return Err(off_boundary());
        };
        whiskers.push(Whisker {
            head,
            before: source_args
                .iter()
                .take(step)
                .map(|arg| arg.to_term())
                .collect(),
            after: source_args
                .iter()
                .skip(step.saturating_add(1))
                .map(|arg| arg.to_term())
                .collect(),
        });
        source = source_child;
        let (_, target_args) = application(target, off_boundary)?;
        let Some(&target_child) = target_args.get(step)
        else {
            return Err(off_boundary());
        };
        target = target_child;
    }
    Ok(WhiskeredCell {
        whiskers: whiskers.into(),
        active: ActiveCell::Redex(InterfacePair::new(
            occurrence.rewrite.clone(),
            source.to_term(),
            target.to_term(),
        )),
    })
}

/// Enumerate the redex occurrences the declared output port unfolds to, each
/// with its position in the derived boundary.
///
/// This is the block's occurrence record, and it is public because
/// [`elaborate_body`] is not its only consumer. A body with two occurrences
/// has no single whiskered composite and is declined one
/// ([`CircuitElaborationError::ManyRedexOccurrences`]), but the two positions
/// are exactly what a rule application needs: the shift-equivalence licence a
/// horizontal composite rests on is not well-posed at a schema's declaration —
/// asking there asks whether every instantiation commutes — and becomes
/// well-posed where the rule is applied, against the cells its rewrite-sorted
/// ports are instantiated by. The record is what carries the two argument
/// paths to that site, so the positions an application fires at are read
/// rather than fabricated.
///
/// # Specification
/// - ensures: one entry per redex occurrence reached by the source reading's
///   unfolding of the declared output port, in left-to-right order, positioned
///   by the argument-index path the unfolding took; a wire consumed twice
///   contributes two entries.
/// - provides: the positions a two-redex body's applications sit at, for the
///   instantiation site that earns their identification.
/// - fails: [`CircuitDerivationError::CyclicWiring`] on a port reachable from
///   itself other than as a redex's own opaque endpoint — the same guard the
///   derivation runs, so the walk stays total on a wiring the derivation
///   refuses; [`CircuitDerivationError::NodeBudget`] on a wiring whose
///   unfolding passes [`CircuitNodeBudget::DEFAULT`], which is the same ceiling
///   the derivation runs under and is charged here too because this is a second
///   traversal of the same reconvergence.
/// - panics: none.
///
/// # Errors
/// See the `- fails:` clause above.
///
/// # Adequacy
/// - hypothesis: L3 — empty, root and nested occurrence lists, distinct and
///   reconvergent redexes, opaque endpoints, cycles and over-budget bodies have
///   exact records or errors; lost duplicates, reversed siblings, inappropriate
///   cycle detection and missing budget checks change them.
/// - witness: `elaborate::tests::two_disjoint_redexes_decline_with_incomparable_positions`
/// - witness: `elaborate::tests::a_reconvergent_redex_is_two_occurrences_of_one_rewrite`
/// - witness: `elaborate::tests::a_cyclic_wiring_elaborates_to_nothing`
/// - witness: `elaborate::tests::occurrence_walk_distinguishes_opaque_roots_and_budget_refusals`
#[inline]
#[spec(ensures: |ref result| match *result {
    | Ok(ref occurrences) => occurrences.len() <= usize::from(CircuitNodeBudget::DEFAULT)
        && occurrences.iter().all(|occurrence| body.nodes.iter().any(|node| matches!(*node, CircuitNode::Redex(ref redex) if redex.rewrite == occurrence.rewrite)))
        && occurrences.iter().zip(occurrences.iter().skip(1)).all(|(first, second)| first.position <= second.position),
    | Err(CircuitDerivationError::NodeBudget { budget }) => budget == CircuitNodeBudget::DEFAULT,
    | Err(CircuitDerivationError::CyclicWiring(ref port)) => body.nodes.iter().any(|node| node.out() == port),
})]
pub fn redex_occurrences(body: &CircuitBody)
-> Result<Vec<RedexOccurrence>, CircuitDerivationError>
{
    /// One step of the occurrence worklist.
    enum Walk<'body>
    {
        /// Resolve a port through the node that binds it.
        Port(&'body Name),
        /// Walk a term, resolving its port leaves.
        Term(TermNode<'body>),
        /// Enter an argument slot.
        Descend(TermPositionIndex),
        /// Leave an argument slot.
        Ascend,
        /// The port's subtree is walked: take it off the active path.
        Leave(&'body Name),
    }

    /// Queue every argument of an application, left to right, under its
    /// index.
    ///
    /// # Specification
    /// - ensures: appends one ascend/term/descend triple per argument, in
    ///   reverse argument order, so the stack enters leftmost arguments first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nullary and two-argument application walks are
    ///   observed as exact occurrence positions; a missing stack delimiter,
    ///   reversed argument order or incorrect index changes those positions.
    /// - witness: `elaborate::tests::two_disjoint_redexes_decline_with_incomparable_positions`
    /// - witness: `elaborate::tests::a_body_with_no_redex_is_the_identity_rewrite`
    #[spec(
        captures: before = stack.len(),
        ensures: stack.get(before ..).is_some_and(|added| added.len().is_multiple_of(3)
            && added.chunks_exact(3).all(|steps| matches!(*steps, [Walk::Ascend, Walk::Term(_), Walk::Descend(_)]))),
    )]
    fn push_args<'body, A>(
        stack: &mut Vec<Walk<'body>>,
        args: A,
    ) where
        A: IntoIterator<Item = TermNode<'body>>,
    {
        let args: Vec<TermNode<'body>> = args.into_iter().collect();
        for (index, arg) in args.iter().copied().enumerate().rev() {
            stack.push(Walk::Ascend);
            stack.push(Walk::Term(arg));
            stack.push(Walk::Descend(TermPositionIndex::from(index)));
        }
    }

    let mut producers: BTreeMap<&Name, &CircuitNode> = BTreeMap::new();
    for node in &body.nodes {
        producers.entry(node.out()).or_insert(node);
    }

    let ceiling = usize::from(CircuitNodeBudget::DEFAULT);
    let mut visited: usize = 0;
    let mut path: BTreeSet<&Name> = BTreeSet::new();
    let mut position: Vec<TermPositionIndex> = Vec::new();
    let mut occurrences: Vec<RedexOccurrence> = Vec::new();
    let mut stack: Vec<Walk<'_>> = vec![Walk::Port(&body.out)];
    while let Some(step) = stack.pop() {
        // The same node-visit charge the derivation makes, for the same
        // reason: this walk is a second traversal of one wiring and inherits
        // its reconvergence cost, so it inherits its ceiling rather than
        // running unbounded beside a bounded one.
        if matches!(step, Walk::Port(_) | Walk::Term(_)) {
            visited = visited.saturating_add(1);
            if visited > ceiling {
                return Err(CircuitDerivationError::NodeBudget {
                    budget: CircuitNodeBudget::DEFAULT,
                });
            }
        }
        match step {
            | Walk::Port(port) => {
                let Some(node) = producers.get(port).copied()
                else {
                    // An interface port: a boundary variable, and no rewrite
                    // happens at it.
                    continue;
                };
                match *node {
                    | CircuitNode::Redex(ref redex) => {
                        occurrences.push(RedexOccurrence::new(
                            redex.rewrite.clone(),
                            position.clone(),
                        ));
                        if matches!(redex.source.view(), TermView::Var(name) if name == port) {
                            continue;
                        }
                        if !path.insert(port) {
                            return Err(CircuitDerivationError::CyclicWiring(port.clone()));
                        }
                        stack.push(Walk::Leave(port));
                        stack.push(Walk::Term(redex.source.to_node()));
                    },
                    | CircuitNode::Frame(ref frame) => {
                        if !path.insert(port) {
                            return Err(CircuitDerivationError::CyclicWiring(port.clone()));
                        }
                        stack.push(Walk::Leave(port));
                        push_args(&mut stack, frame.args.iter().map(FreeTerm::to_node));
                    },
                }
            },
            | Walk::Term(term) => match term.view() {
                | TermView::Var(name) => stack.push(Walk::Port(name)),
                | TermView::Ctor { args, .. } | TermView::Op { args, .. } => {
                    push_args(&mut stack, args);
                },
            },
            | Walk::Descend(index) => position.push(index),
            | Walk::Ascend => {
                position.pop();
            },
            | Walk::Leave(port) => {
                path.remove(port);
            },
        }
    }
    Ok(occurrences)
}

/// A term's distinct variable leaves, in first-occurrence left-to-right
/// order.
///
/// # Specification
/// - ensures: every variable leaf appears exactly once, ordered by its first
///   occurrence: the declaration order the boundary language's `r(t₁, …, tₙ)`
///   instantiates in.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — ground, single-variable and repeated mixed-variable
///   sources are observed through exact instantiated endpoints; sorting,
///   retaining duplicate names or omitting a first occurrence changes them.
/// - witness: `elaborate::tests::instantiation_observes_zero_arity_and_first_occurrence_order`
/// - witness: `elaborate::tests::a_repeated_source_variable_consumes_one_argument`
#[spec(ensures: |ref names| term.to_node().vars().all(|name| names.contains(name))
    && names.iter().enumerate().all(|(index, name)| term.to_node().vars().any(|leaf| leaf == name)
        && !names.iter().take(index).any(|prior| prior == name))
    && names.iter().zip(names.iter().skip(1)).all(|(first, second)| term.to_node().vars().position(|name| name == first)
        .zip(term.to_node().vars().position(|name| name == second)).is_some_and(|(first, second)| first < second)))]
fn distinct_vars(term: &FreeTerm) -> Vec<Name>
{
    let mut distinct: Vec<Name> = Vec::new();
    for name in term.to_node().vars() {
        if !distinct.contains(name) {
            distinct.push(name.clone());
        }
    }
    distinct
}

/// Apply a variable substitution to a term.
///
/// # Specification
/// - ensures: every variable leaf bound by `bindings` is replaced by its term
///   and every other leaf is kept; applications keep their head, alphabet and
///   argument order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — bound and unbound root/nested leaves, images containing
///   another bound name and mixed application alphabets have exact output
///   terms; repeated substitution, head changes and a dropped unbound leaf
///   change those terms.
/// - witness: `elaborate::tests::substitution_is_simultaneous_and_preserves_unbound_leaves`
#[spec(ensures: |ref result| result.to_node().vars().eq(term.to_node().vars().flat_map(|name| {
    bindings.get(name).into_iter().flat_map(|image| image.to_node().vars())
        .chain(core::iter::once(name).filter(move |_| !bindings.contains_key(name)))
})))]
fn substitute(
    term: &FreeTerm,
    bindings: &BTreeMap<Name, FreeTerm>,
) -> FreeTerm
{
    term.replace_vars(|name| match bindings.get(name) {
        | Some(bound) => Maybe::Present(bound.to_node()),
        | None => Maybe::Absent(leaf_image::Absent::Kept),
    })
}

#[cfg(test)]
mod tests
{

    use super::*;
    use crate::circuit::CircuitFrame;

    /// `node : p(x) ==> (x′); node : add(x′, y) --> (z);` with `z` declared:
    /// the congruence body of the ruled block form with one of its two
    /// rewrite-sorted ports, which is the shape the whiskering construction
    /// `f(t̄, ρ, ū)` spells.
    ///
    /// # Specification
    /// trivial.
    fn one_redex_body() -> CircuitBody
    {
        CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("x\u{2032}"),
                    "x\u{2032}",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("x\u{2032}"), FreeTerm::var("y")],
                    "z",
                )),
            ],
            "z",
        )
    }

    #[test]
    fn a_sorted_port_binds_two_distinct_endpoints()
    {
        // `rule p : Nat ==> Nat` writes the boundary sort and no terms, so the
        // pair it binds is two endpoints the sort alone does not name.
        let pair = RewritePort::sorted("p", "Nat").interface();
        assert_eq!(
            pair,
            InterfacePair::new("p", FreeTerm::var("p⟨source⟩"), FreeTerm::var("p⟨target⟩"))
        );
    }

    #[test]
    fn a_pinned_port_binds_the_terms_it_writes()
    {
        // `rule p : x ==> Succ(x)` names its own endpoints, so the pair is
        // those terms rather than minted variables.
        let pair = RewritePort::pinned(
            "p",
            FreeTerm::var("x"),
            FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
        )
        .interface();
        assert_eq!(
            InterfacePair::new(
                "p",
                FreeTerm::var("x"),
                FreeTerm::ctor("Succ", [FreeTerm::var("x")])
            ),
            pair,
            "the pinned form's interface pair is what its declaration writes"
        );
    }

    #[test]
    fn instantiating_a_port_unifies_the_source_and_binds_the_target()
    {
        // `node : p(x) ==> (x′)` against `rule p : Nat ==> Nat`: the source
        // takes the line's input wiring, and the target — which the sort does
        // not name — is the output port, the opaque endpoint the derivation
        // reads as a leaf.
        let redex = RewritePort::sorted("p", "Nat")
            .interface()
            .instantiate([FreeTerm::var("x")], "x\u{2032}")
            .expect("a one-argument line matches a one-endpoint source");
        assert_eq!(
            CircuitRedex::new(
                "p",
                FreeTerm::var("x"),
                FreeTerm::var("x\u{2032}"),
                "x\u{2032}"
            ),
            redex,
            "the instantiation is the redex the boundary derivation consumes"
        );
    }

    #[test]
    fn instantiating_a_pinned_port_substitutes_into_its_target()
    {
        // `rule p : x ==> Succ(x)` fired at `a`: the source binds the target's
        // variable, so the target is a term rather than the output port.
        let redex = RewritePort::pinned(
            "p",
            FreeTerm::var("x"),
            FreeTerm::ctor("Succ", [FreeTerm::var("x")]),
        )
        .interface()
        .instantiate([FreeTerm::var("a")], "w")
        .expect("a one-argument line matches a one-variable source");
        assert_eq!(
            CircuitRedex::new(
                "p",
                FreeTerm::var("a"),
                FreeTerm::ctor("Succ", [FreeTerm::var("a")]),
                "w"
            ),
            redex,
            "the pinned target is instantiated, not replaced by the output port"
        );
    }

    #[test]
    fn a_repeated_source_variable_consumes_one_argument()
    {
        // `rule p : add(a, a) ==> a` has one distinct source variable, so the
        // line supplies one argument and both occurrences take it.
        let redex = RewritePort::pinned(
            "p",
            FreeTerm::op("add", [FreeTerm::var("a"), FreeTerm::var("a")]),
            FreeTerm::var("a"),
        )
        .interface()
        .instantiate([FreeTerm::var("u")], "z")
        .expect("one distinct source variable takes one argument");
        assert_eq!(
            CircuitRedex::new(
                "p",
                FreeTerm::op("add", [FreeTerm::var("u"), FreeTerm::var("u")]),
                FreeTerm::var("u"),
                "z"
            ),
            redex,
            "a repeated source variable is bound once and used twice"
        );
    }

    #[test]
    fn an_instantiation_that_does_not_unify_declines()
    {
        // Two arguments against a one-endpoint source: the line's input wiring
        // is not this port's interface, and the decline says so by count.
        let declined = RewritePort::sorted("p", "Nat")
            .interface()
            .instantiate([FreeTerm::var("x"), FreeTerm::var("y")], "z");
        assert_eq!(
            Err(PortInstantiationError::SourceArity {
                rewrite: "p".into(),
                expected: PortArgumentCount::from(1_usize),
                supplied: PortArgumentCount::from(2_usize),
            }),
            declined,
            "an instantiation that does not unify is a typed decline"
        );
    }

    #[test]
    fn a_target_endpoint_no_wire_supplies_declines()
    {
        // `rule p : x ==> Succ(y)`: `y` is neither bound by the source nor the
        // lone opaque endpoint the output port supplies, so no wire carries it.
        let declined = RewritePort::pinned(
            "p",
            FreeTerm::var("x"),
            FreeTerm::ctor("Succ", [FreeTerm::var("y")]),
        )
        .interface()
        .instantiate([FreeTerm::var("a")], "w");
        assert_eq!(
            Err(PortInstantiationError::UnboundTargetEndpoint {
                rewrite: "p".into(),
                endpoints: vec![Name::from("y")].into(),
            }),
            declined,
            "a target endpoint the wiring cannot supply is a typed decline"
        );
    }

    #[test]
    fn a_single_redex_block_elaborates_to_a_whiskered_cell()
    {
        let cell = elaborate_body(&one_redex_body()).expect("one redex whiskers into one frame");
        assert_eq!(
            WhiskeredCell::whisker(
                FrameHead::Op("add".into()),
                [],
                WhiskeredCell::redex(InterfacePair::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("x\u{2032}")
                )),
                [FreeTerm::var("y")],
            ),
            cell,
            "a redex inside a frame is the whiskering `add(rho, y)`"
        );
        assert_eq!(
            Maybe::Present(vec![TermPositionIndex::from(0_usize)]),
            cell.active_position(),
            "and its active position is the argument slot the redex sits in"
        );
    }

    #[test]
    fn a_redex_under_two_frames_whiskers_outermost_first()
    {
        // `node : p(n) ==> (m); node : Succ(m) --> (s); node : add(w, s) --> (z);`
        // — the redex sits in the second argument of `add`, inside the first
        // argument of `Succ`.
        let body = CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("n"),
                    FreeTerm::var("m"),
                    "m",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Ctor("Succ".into()),
                    [FreeTerm::var("m")],
                    "s",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("w"), FreeTerm::var("s")],
                    "z",
                )),
            ],
            "z",
        );
        let cell = elaborate_body(&body).expect("one redex whiskers into two frames");
        assert_eq!(
            WhiskeredCell::whisker(
                FrameHead::Op("add".into()),
                [FreeTerm::var("w")],
                WhiskeredCell::whisker(
                    FrameHead::Ctor("Succ".into()),
                    [],
                    WhiskeredCell::redex(InterfacePair::new(
                        "p",
                        FreeTerm::var("n"),
                        FreeTerm::var("m")
                    )),
                    [],
                ),
                [],
            ),
            cell,
            "the outermost frame is the outermost whisker"
        );
        assert_eq!(
            Maybe::Present(vec![
                TermPositionIndex::from(1_usize),
                TermPositionIndex::from(0_usize)
            ]),
            cell.active_position(),
            "the active position reads the argument slots root-first"
        );
    }

    #[test]
    fn a_redex_at_the_root_needs_no_whisker()
    {
        let body = CircuitBody::new(
            [CircuitNode::Redex(CircuitRedex::new(
                "p",
                FreeTerm::var("x"),
                FreeTerm::var("x\u{2032}"),
                "x\u{2032}",
            ))],
            "x\u{2032}",
        );
        let cell = elaborate_body(&body).expect("a bare redex is its own composite");
        assert_eq!(
            WhiskeredCell::redex(InterfacePair::new(
                "p",
                FreeTerm::var("x"),
                FreeTerm::var("x\u{2032}")
            )),
            cell,
            "no frame encloses it, so no whisker wraps it"
        );
        assert_eq!(
            Maybe::Present(Vec::new()),
            cell.active_position(),
            "the root is the empty argument path"
        );
    }

    #[test]
    fn a_body_with_no_redex_is_the_identity_rewrite()
    {
        // A body whose statements are all frames is a 1-cell definition; read
        // as a 2-cell it is the empty rewrite at the term it builds.
        let body = CircuitBody::new(
            [CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Ctor("Succ".into()),
                [FreeTerm::var("n")],
                "m",
            ))],
            "m",
        );
        let cell = elaborate_body(&body).expect("a frames-only wiring is acyclic");
        assert_eq!(
            WhiskeredCell::here(FreeTerm::ctor("Succ", [FreeTerm::var("n")])),
            cell,
            "no redex means `here(t)` at the frame's own term"
        );
    }

    #[test]
    fn an_identity_composite_has_no_active_position()
    {
        assert_eq!(
            Maybe::Absent(active_position::Absent::Identity),
            WhiskeredCell::here(FreeTerm::var("z")).active_position(),
            "an identity composite is nowhere active"
        );
        let nested = WhiskeredCell::whisker(
            FrameHead::Ctor("F".into()),
            [FreeTerm::var("before")],
            WhiskeredCell::here(FreeTerm::var("z")),
            [],
        );
        assert_eq!(
            nested.active_position(),
            Maybe::Absent(active_position::Absent::Identity)
        );
    }

    #[test]
    fn a_nested_whisker_reports_its_argument_path()
    {
        // Built directly, so the path is pinned to the count of unchanged
        // arguments left of the active slot at each level rather than to a
        // constant.
        let cell = WhiskeredCell::whisker(
            FrameHead::Op("f".into()),
            [FreeTerm::var("a")],
            WhiskeredCell::whisker(
                FrameHead::Op("g".into()),
                [FreeTerm::var("b"), FreeTerm::var("c")],
                WhiskeredCell::redex(InterfacePair::new(
                    "p",
                    FreeTerm::var("s"),
                    FreeTerm::var("t"),
                )),
                [],
            ),
            [FreeTerm::var("d")],
        );
        assert_eq!(
            Maybe::Present(vec![
                TermPositionIndex::from(1_usize),
                TermPositionIndex::from(2_usize)
            ]),
            cell.active_position(),
            "each level contributes the index of its active argument slot"
        );
    }

    #[test]
    fn two_disjoint_redexes_decline_with_incomparable_positions()
    {
        // The ruled `cong2` body: two redexes sharing no port name, whiskered
        // into one frame. Their positions are incomparable, which is the
        // horizontal composite licensed only against an earned witness.
        let body = CircuitBody::new(
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
        );
        assert_eq!(
            Err(CircuitElaborationError::ManyRedexOccurrences {
                occurrences: vec![
                    RedexOccurrence::new("p", [TermPositionIndex::from(0_usize)]),
                    RedexOccurrence::new("q", [TermPositionIndex::from(1_usize)]),
                ]
                .into(),
            }),
            elaborate_body(&body),
            "two redex occurrences decline, carrying the positions the guard asks about"
        );
    }

    #[test]
    fn a_reconvergent_redex_is_two_occurrences_of_one_rewrite()
    {
        // One redex output feeding both arguments of one frame: the wire is
        // unfolded at each consumption, so the composite would hold the same
        // rewrite at two positions.
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
        assert_eq!(
            Err(CircuitElaborationError::ManyRedexOccurrences {
                occurrences: vec![
                    RedexOccurrence::new("p", [TermPositionIndex::from(0_usize)]),
                    RedexOccurrence::new("p", [TermPositionIndex::from(1_usize)]),
                ]
                .into(),
            }),
            elaborate_body(&body),
            "a shared wire is two occurrences of one rewrite, not one position"
        );
    }

    #[test]
    fn a_cyclic_wiring_elaborates_to_nothing()
    {
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
            redex_occurrences(&body),
            Err(CircuitDerivationError::CyclicWiring("a".into()))
        );
        assert_eq!(
            Err(CircuitElaborationError::Derivation(
                CircuitDerivationError::CyclicWiring("a".into())
            )),
            elaborate_body(&body),
            "no boundary pair means no composite, and the decline names the port"
        );
    }

    #[test]
    fn instantiation_observes_zero_arity_and_first_occurrence_order()
    {
        let ground = InterfacePair::new(
            "ground",
            FreeTerm::ctor("Zero", []),
            FreeTerm::ctor("Succ", [FreeTerm::ctor("Zero", [])]),
        );
        assert_eq!(
            ground.instantiate([], "out"),
            Ok(CircuitRedex::new(
                "ground",
                ground.source.clone(),
                ground.target.clone(),
                "out"
            ))
        );
        assert_eq!(
            ground.instantiate([FreeTerm::var("extra")], "out"),
            Err(PortInstantiationError::SourceArity {
                rewrite: "ground".into(),
                expected: PortArgumentCount::from(0_usize),
                supplied: PortArgumentCount::from(1_usize)
            })
        );
        let sorted = RewritePort::sorted("p", "Nat").interface();
        assert_eq!(
            sorted.instantiate([], "out"),
            Err(PortInstantiationError::SourceArity {
                rewrite: "p".into(),
                expected: PortArgumentCount::from(1_usize),
                supplied: PortArgumentCount::from(0_usize)
            })
        );
        let pair = InterfacePair::new(
            "ordered",
            FreeTerm::op("f", [
                FreeTerm::var("b"),
                FreeTerm::var("a"),
                FreeTerm::var("b"),
            ]),
            FreeTerm::op("g", [FreeTerm::var("a"), FreeTerm::var("b")]),
        );
        assert_eq!(
            pair.instantiate([FreeTerm::var("U"), FreeTerm::var("V")], "out"),
            Ok(CircuitRedex::new(
                "ordered",
                FreeTerm::op("f", [
                    FreeTerm::var("U"),
                    FreeTerm::var("V"),
                    FreeTerm::var("U")
                ]),
                FreeTerm::op("g", [FreeTerm::var("V"), FreeTerm::var("U")]),
                "out"
            ))
        );
        let unbound = InterfacePair::new(
            "missing",
            FreeTerm::var("x"),
            FreeTerm::op("f", [
                FreeTerm::var("z"),
                FreeTerm::var("y"),
                FreeTerm::var("z"),
            ]),
        );
        assert_eq!(
            unbound.instantiate([FreeTerm::var("a")], "out"),
            Err(PortInstantiationError::UnboundTargetEndpoint {
                rewrite: "missing".into(),
                endpoints: [Name::from("z"), Name::from("y")].into()
            })
        );
    }

    #[test]
    fn application_and_whisker_positions_decline_off_boundary()
    {
        let variable = FreeTerm::var("x");
        let mut calls = 0_usize;
        assert_eq!(
            application(variable.to_node(), || {
                calls = calls.saturating_add(1);
                active_position::Absent::Identity
            }),
            Err(active_position::Absent::Identity)
        );
        assert_eq!(calls, 1);
        for (term, expected_head, expected_args) in [
            (
                FreeTerm::ctor("Zero", []),
                FrameHead::Ctor("Zero".into()),
                vec![],
            ),
            (
                FreeTerm::op("f", [FreeTerm::var("x"), FreeTerm::var("y")]),
                FrameHead::Op("f".into()),
                vec![FreeTerm::var("x"), FreeTerm::var("y")],
            ),
        ] {
            let (head, args) = application::<active_position::Absent, _>(term.to_node(), || {
                panic!("an application does not call the refusal callback")
            })
            .expect("application");
            assert_eq!(head, expected_head);
            assert_eq!(
                args.into_iter().map(TermNode::to_term).collect::<Vec<_>>(),
                expected_args
            );
        }
        let one = FreeTerm::op("f", [FreeTerm::var("x")]);
        let two = FreeTerm::op("f", [FreeTerm::var("x"), FreeTerm::var("y")]);
        for (source, target, index) in [
            (variable.clone(), one.clone(), 0_usize),
            (one.clone(), variable, 0),
            (one.clone(), two.clone(), 1),
            (two, one, 1),
        ] {
            let occurrence = RedexOccurrence::new("p", [TermPositionIndex::from(index)]);
            assert_eq!(
                whisker_along(&DerivedBoundaries { source, target }, &occurrence),
                Err(CircuitElaborationError::PositionOffBoundary {
                    rewrite: occurrence.rewrite,
                    position: occurrence.position
                })
            );
        }
    }

    #[test]
    fn substitution_is_simultaneous_and_preserves_unbound_leaves()
    {
        let image = FreeTerm::ctor("Image", [FreeTerm::var("y")]);
        let bindings = BTreeMap::from([
            (Name::from("x"), image.clone()),
            (Name::from("y"), FreeTerm::var("z")),
        ]);
        let source = FreeTerm::op("f", [
            FreeTerm::var("x"),
            FreeTerm::ctor("G", [FreeTerm::var("y")]),
            FreeTerm::var("u"),
        ]);
        assert_eq!(
            substitute(&source, &bindings),
            FreeTerm::op("f", [
                image.clone(),
                FreeTerm::ctor("G", [FreeTerm::var("z")]),
                FreeTerm::var("u")
            ])
        );
        assert_eq!(substitute(&FreeTerm::var("x"), &bindings), image);
        assert_eq!(
            substitute(&FreeTerm::var("u"), &bindings),
            FreeTerm::var("u")
        );
    }

    #[test]
    fn occurrence_walk_distinguishes_opaque_roots_and_budget_refusals()
    {
        assert_eq!(redex_occurrences(&CircuitBody::new([], "x")), Ok(vec![]));
        let opaque = CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("w"),
                    FreeTerm::var("t"),
                    "w",
                )),
                CircuitNode::Redex(CircuitRedex::new(
                    "later",
                    FreeTerm::var("w"),
                    FreeTerm::var("u"),
                    "w",
                )),
            ],
            "w",
        );
        assert_eq!(
            redex_occurrences(&opaque),
            Ok(vec![RedexOccurrence::new("p", [])])
        );
        let mut nodes = Vec::new();
        let mut previous = Name::from("x");
        for level in 0 .. 20_usize {
            let out = Name::from(alloc::format!("w{level}"));
            nodes.push(CircuitNode::Frame(CircuitFrame::new(
                FrameHead::Op("double".into()),
                [FreeTerm::var(previous.clone()), FreeTerm::var(previous)],
                out.clone(),
            )));
            previous = out;
        }
        let body = CircuitBody::new(nodes, previous);
        let error = CircuitDerivationError::NodeBudget {
            budget: CircuitNodeBudget::DEFAULT,
        };
        assert_eq!(redex_occurrences(&body), Err(error.clone()));
        assert_eq!(
            elaborate_body(&body),
            Err(CircuitElaborationError::Derivation(error))
        );
    }
}
