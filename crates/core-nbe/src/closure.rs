//! Both closure spaces, and the environment they close over.
//!
//! # Two spaces, one entry operation
//!
//! The core language has two term families, so a suspended body is one of two
//! things:
//!
//! - [`ValueClosure`] suspends a **value** body: the shape a quote takes, its
//!   type suspended whole over the environment its codes read.
//! - [`CompClosure`] suspends a **computation** body: the shape a lambda, a
//!   thunk, a bind continuation and a case branch all take.
//!
//! Both spaces close over the same [`Environment`], so entering a closure is
//! one operation over either, for the same reason the two faces of [the
//! domain] are named on one type.
//!
//! # The environment mirrors the context's two zones
//!
//! A closure captures what its free variables stand for, and a free variable
//! names a zone as well as an index, so the environment carries the same two
//! flat stacks the typing context does. Mirroring is forced rather than
//! preferred: an environment with one stack could not answer a linear
//! occurrence at all, and reconstructing which stack an index meant from a
//! depth comparison is exactly the ambiguity the zone on the occurrence exists
//! to remove.
//!
//! Entries are domain value ids, so an environment is two flat vectors of
//! `Copy` ids and capturing one is a vector clone rather than a graph walk.
//!
//! # Closure spaces
//!
//! `ValueClosure` suspends a source value or a virtual
//! value-type/computation-type quote, without allocating synthetic source
//! syntax during evaluation. `CompClosure::body` retains source syntax or
//! native transport and argument-application continuations. Both spaces capture
//! the two-zone `Environment`; entering a closure extends that environment and
//! evaluates its body. Entries are `Copy` ids, so capturing an environment
//! clones two flat vectors.
//!
//! [the domain]: crate::domain

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

use crate::arena::CompClosureId;
use crate::arena::DomainValueId;

/// The offset of one entry within a zone of the environment.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct EntryOffset(usize);

/// The number of entries one zone of an environment holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EnvironmentDepth(usize);

impl From<usize> for EnvironmentDepth
{
    /// Read a `usize` as a zone depth.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: usize) -> Self
    {
        Self(depth)
    }
}

impl From<EnvironmentDepth> for usize
{
    /// Read the depth back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: EnvironmentDepth) -> Self
    {
        depth.0
    }
}

/// What a closure's free variables stand for: two flat stacks of domain value
/// ids, one per zone, innermost binding last.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Environment
{
    /// The intuitionistic zone's bindings.
    intuitionistic: Vec<DomainValueId>,
    /// The linear zone's bindings.
    linear: Vec<DomainValueId>,
}

impl Environment
{
    /// The empty environment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The number of bindings a zone holds.
    ///
    /// # Specification
    /// - requires: nothing; both zones answer, and an unbound zone answers
    ///   zero.
    /// - ensures: the number of bindings that zone holds, which is one more
    ///   than the greatest index bound in it.
    /// - provides: the bound `entry_offset` resolves an index against, and the
    ///   level a readback counts a fresh variable from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty zones and unequal one- and two-binding zones
    ///   are observed by their exact depths; selecting the other zone, biasing
    ///   the count or treating an empty zone as bound changes a result.
    /// - witness: `closure::tests::the_zones_resolve_one_index_to_two_bindings`
    /// - witness: `closure::tests::an_index_past_the_depth_resolves_to_nothing`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == match zone {
        | Zone::Intuitionistic => self.intuitionistic.len(),
        | Zone::Linear => self.linear.len(),
    })]
    pub fn depth(
        &self,
        zone: Zone,
    ) -> EnvironmentDepth
    {
        EnvironmentDepth(match zone {
            Zone::Intuitionistic => self.intuitionistic.len(),
            Zone::Linear => self.linear.len(),
        })
    }

    /// Extend a zone with one binding.
    ///
    /// # Specification
    /// - requires: `bound` resolves in the domain arena this environment is
    ///   read against; the environment stores the id and never dereferences it.
    /// - ensures: the zone's depth is one greater, index zero of that zone
    ///   names `bound`, every previously bound index of that zone is reachable
    ///   at one more than it was, and the other zone is untouched.
    /// - provides: the binder-entering half of every rule that goes under a
    ///   binder, and the counterpart of the typing context's own binder
    ///   opening. The clause states the extended zone's depth, the new
    ///   innermost binding, the shift of the previously innermost one, and the
    ///   other zone's depth; the shift of every deeper index and the other
    ///   zone's contents would need owned entry snapshots, which the pinned
    ///   expansion evaluates even in a non-enforcing build.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is which zone is pushed,
    ///   separated by extending each zone with the other's depth asserted
    ///   unmoved, and by the shift of an already-bound index in the extended
    ///   zone. Appending to the wrong zone, clearing its peer or dropping the
    ///   shifted outer binding changes a lookup or depth.
    /// - witness: `closure::tests::the_zones_resolve_one_index_to_two_bindings`
    /// - witness: `closure::tests::an_index_past_the_depth_resolves_to_nothing`
    #[inline]
    #[spec(
        captures: [
            entry_intuitionistic = self.intuitionistic.len(),
            entry_linear = self.linear.len(),
            entry_innermost = match zone {
                | Zone::Intuitionistic => self.intuitionistic.last().copied(),
                | Zone::Linear => self.linear.last().copied(),
            },
        ],
        ensures: match zone {
            | Zone::Intuitionistic => {
                self.intuitionistic.len() == entry_intuitionistic.saturating_add(1_usize)
                    && self.intuitionistic.last() == Some(&bound)
                    && self.intuitionistic.len().checked_sub(2_usize)
                        .and_then(|offset| self.intuitionistic.get(offset)).copied() == entry_innermost
                    && self.linear.len() == entry_linear
            },
            | Zone::Linear => {
                self.linear.len() == entry_linear.saturating_add(1_usize)
                    && self.linear.last() == Some(&bound)
                    && self.linear.len().checked_sub(2_usize)
                        .and_then(|offset| self.linear.get(offset)).copied() == entry_innermost
                    && self.intuitionistic.len() == entry_intuitionistic
            },
        }
    )]
    pub fn extend(
        &mut self,
        zone: Zone,
        bound: DomainValueId,
    )
    {
        match zone {
            Zone::Intuitionistic => self.intuitionistic.push(bound),
            Zone::Linear => self.linear.push(bound),
        }
    }

    /// What a bound occurrence stands for.
    ///
    /// The index counts binders outward from the use site within its own zone,
    /// so index zero names the innermost binding of that zone.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range index is admissible input.
    /// - ensures: the id the named binding holds.
    /// - provides: the variable rule of an evaluator, and the one place the two
    ///   zones' index spaces are read.
    /// - fails: returns `None` when the index counts past the zone's bindings,
    ///   which an evaluator turns into a fresh neutral rather than a panic.
    /// - panics: none — the index arithmetic is checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the zone selection and the
    ///   index arithmetic, separated by the innermost and an outer binding of a
    ///   two-deep zone, the first index past the depth, and one index resolved
    ///   in each zone with the other zone holding a different id at the same
    ///   index. Empty zones and the maximal index cover refusal boundaries;
    ///   wrong-zone reads, reversed indexing and wrapped subtraction change an
    ///   answer.
    /// - witness: `closure::tests::the_zones_resolve_one_index_to_two_bindings`
    /// - witness: `closure::tests::an_index_past_the_depth_resolves_to_nothing`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| [
        ret.is_some()
            == usize::try_from(u32::from(index)).is_ok_and(|counted| counted < self.depth(zone).0),
        ret == entry_offset(self.depth(zone), index).and_then(|offset| match zone {
            | Zone::Intuitionistic => self.intuitionistic.get(offset.0).copied(),
            | Zone::Linear => self.linear.get(offset.0).copied(),
        }),
    ])]
    pub fn lookup(
        &self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Option<DomainValueId>
    {
        let offset = entry_offset(self.depth(zone), index)?;
        match zone {
            Zone::Intuitionistic => self.intuitionistic.get(offset.0).copied(),
            Zone::Linear => self.linear.get(offset.0).copied(),
        }
    }

    /// Every binding one zone holds, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn bindings(
        &self,
        zone: Zone,
    ) -> &[DomainValueId]
    {
        match zone {
            Zone::Intuitionistic => &self.intuitionistic,
            Zone::Linear => &self.linear,
        }
    }
}

/// Resolve a de Bruijn index against a zone of `depth` bindings.
///
/// # Specification
/// - requires: nothing — every index and every depth is admissible input.
/// - ensures: the stack offset of the named binding, `depth - index - 1`,
///   exactly when the index counts within `depth`.
/// - provides: the one arithmetic both zones' lookups share.
/// - fails: returns `None` when the index counts past the zone's bindings.
/// - panics: none — both subtractions are checked.
///
/// # Adequacy
/// - hypothesis: L3 — the two decision surfaces are the two checked
///   subtractions, separated by the innermost binding of a two-deep zone, an
///   outer binding, the first index past the depth, and an index read against
///   an empty zone, each observed through the lookup that reports on it. The
///   maximal index is refused in both zones; accepting an out-of-range offset,
///   reversing the stack or losing a subtraction changes the result.
/// - witness: `closure::tests::the_zones_resolve_one_index_to_two_bindings`
/// - witness: `closure::tests::an_index_past_the_depth_resolves_to_nothing`
#[inline]
#[spec(ensures: |ret| match (usize::try_from(u32::from(index)), ret) {
    | (Ok(counted), Some(offset)) => counted < depth.0
        && offset.0.checked_add(counted) == depth.0.checked_sub(1_usize),
    | (Ok(counted), None) => counted >= depth.0,
    | (Err(_), offset) => offset.is_none(),
})]
fn entry_offset(
    depth: EnvironmentDepth,
    index: DeBruijnIndex,
) -> Option<EntryOffset>
{
    let index = usize::try_from(u32::from(index)).ok()?;
    let remaining = depth.0.checked_sub(index)?;
    let offset = remaining.checked_sub(1_usize)?;
    Some(EntryOffset(offset))
}

/// A source value or a native quotation of an already existing type root.
///
/// Native type obligations use the same captured environments as source quotes,
/// without mutating the source arena merely to manufacture a quote node.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueBody
{
    /// An ordinary source value, including an explicit quote or static lambda.
    Source(ValueId),
    /// A value-type quotation created by native conversion.
    ValueType(gandr_core_term::ValueTypeId),
    /// A computation-type quotation created by native conversion.
    CompType(gandr_core_term::CompTypeId),
}

/// A suspended **value** body with the environment its free variables stand in.
///
/// Quotes and static lambdas suspend a value body in this environment.
/// [`CompClosure`] carries the corresponding suspended computation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueClosure
{
    /// The core value body, unevaluated.
    body: ValueBody,
    /// What the body's free variables stand for.
    environment: Environment,
}

impl ValueClosure
{
    /// Close `body` over `environment`.
    ///
    /// # Specification
    /// - requires: `environment` binds every occurrence free in `body` in the
    ///   zone that occurrence names; a body and an environment carry no shared
    ///   provenance, so the pairing is the caller's claim.
    /// - ensures: the closure carries exactly the body and environment offered,
    ///   unevaluated.
    /// - provides: the delayed substitution a value binder is represented by,
    ///   which is why the constructor is crate-private: the arena is the one
    ///   producer that pairs the two.
    /// - fails: never — an environment too shallow for the body surfaces where
    ///   the body is entered, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed quotes and quotes over one- and two-binding
    ///   environments are observed by the suspended body, captured lookup and
    ///   code comparisons; changing the body, dropping a binding or reading the
    ///   wrong index changes an observation.
    /// - witness: `eval::tests::normalizes_beta_redex`
    /// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.body == body)]
    pub(crate) fn new(
        body: ValueBody,
        environment: Environment,
    ) -> Self
    {
        Self { body, environment }
    }

    /// The suspended body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn body(&self) -> ValueBody
    {
        self.body
    }

    /// The captured environment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn environment(&self) -> &Environment
    {
        &self.environment
    }
}

/// The eliminator a constructorwise continuation applies at the next part:
/// transport along an element path, or a ride along a flow.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Mover
{
    /// Transport along an element path.
    Transport,
    /// Ride along a flow.
    Ride,
}

/// A suspended body, either source syntax or a native continuation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompBody
{
    /// An ordinary core computation.
    Source(ComputationId),
    /// After the first component returned, transport the second component.
    TransportPair
    {
        /// The second component's path.
        path: DomainValueId,
        /// The second component's operand.
        value: DomainValueId,
    },
    /// Return a pair of the held first component and the newly bound second.
    Pair(DomainValueId),
    /// Return the bound value: the continuation `x. return x` that F-η binds a
    /// computation one bind short into.
    Returned,
    /// Enter `first` at the bound value and bind its result into `then`: the
    /// continuation `x. (N to y. P)` associativity makes two binds in a row
    /// into, built from the two closures as they stand.
    Then
    {
        /// The inner continuation, `x. N`.
        first: CompClosureId,
        /// The outer continuation, `y. P`, still closed over its own
        /// environment.
        then: CompClosureId,
    },
    /// Ride the bound value along `flow` in `motive`: the continuation `x.
    /// ride(P, g, x)` a composite's first leg binds into.
    RideAlong
    {
        /// The ride's motive, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The flow the bound value rides along next.
        flow: DomainValueId,
    },
    /// The body of the thunk a function flow rides a function to: forced, it
    /// returns the lambda [`Self::RideArgument`] enters at the argument.
    RideFunction
    {
        /// The ride's motive, `El(x)`, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The function flow, holding the domain and codomain flows.
        flow: DomainValueId,
        /// The function ridden.
        function: DomainValueId,
    },
    /// `a'. a ← ride(El, d, a'); b ← force f a; ride(El, c, b)`: the ridden
    /// function's body at the bound argument.
    RideArgument
    {
        /// The ride's motive, `El(x)`, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The function flow, holding the domain and codomain flows.
        flow: DomainValueId,
        /// The function ridden.
        function: DomainValueId,
    },
    /// Apply the held thunk, forced, to the bound value: the continuation `a.
    /// force f a`.
    ForceApplied(DomainValueId),
    /// After a flow product's left component rode, ride the right one along
    /// the second flow in the same motive and pair them: the continuation `x.
    /// y ← ride(P, g, b); return (x, y)` the product's reduct binds into.
    RidePair
    {
        /// The ride's motive, `El(x)`, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The second flow.
        flow: DomainValueId,
        /// The right component.
        value: DomainValueId,
    },
    /// After `moved` components moved, move the next in its own part of the
    /// product motive, or return the tuple of all of them: the continuation
    /// `xᵢ. xᵢ₊₁ ← step(Pᵢ₊₁, p, vᵢ₊₁); …; return (x₀, …)` a product motive's
    /// reduct binds each component into. The components moved so far are the
    /// closure's environment, the latest innermost.
    Components
    {
        /// Transport or ride.
        mover: Mover,
        /// The product motive, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The path or flow every component moves along.
        along: DomainValueId,
        /// The tuple moved.
        source: DomainValueId,
        /// How many components have moved once this continuation binds.
        moved: gandr_core_term::ComponentCount,
    },
    /// Return the bound value injected at this summand: the continuation `x.
    /// return inj(x)` a sum motive's reduct binds the payload into.
    Inject(gandr_kernel_term::Summand),
    /// After a cell's head moved, move its tail in the list motive and return
    /// the cell: the continuation `h. t ← step(List E, p, tail); return
    /// cons(h, t)` a list motive's reduct binds the head into.
    MoveTail
    {
        /// Transport or ride.
        mover: Mover,
        /// The list motive, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The path or flow the tail moves along.
        along: DomainValueId,
        /// The cell's tail.
        tail: DomainValueId,
    },
    /// Return the cell of the held head and the newly bound tail.
    Cons(DomainValueId),
    /// Transport the bound value along the rest of a word in the same motive:
    /// the continuation `y. tr(P, u, y)` the transport along a word's first
    /// letter binds into.
    AlongWord
    {
        /// The transport's motive, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The rest of the word.
        rest: DomainValueId,
    },
    /// Transport the bound value along a composite's second path in the same
    /// motive: the continuation `y. tr(P, q, y)` the transport along `p then
    /// q`'s first path binds into. Transport is pure, so a first leg that
    /// sticks is bound as the value it stands for.
    AlongThen
    {
        /// The transport's motive, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The composite's second path.
        second: DomainValueId,
    },
    /// Return the held word's first letter before the newly bound word: the
    /// continuation `w. return ℓ ∷ w` the transport of a word `ℓ ∷ p` in a
    /// singleton family binds `p`'s transport into.
    Prefixed(DomainValueId),
    /// After a held operand of a singleton family's transport ran, transport
    /// what it returned along the path, or stick the transport over the
    /// operand when it returned a held endpoint again: the continuation `v.
    /// tr(P, q, v)` a composite over a call binds the call's run into.
    Appending
    {
        /// The singleton family, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The path the operand moves along.
        path: DomainValueId,
        /// The held operand.
        operand: DomainValueId,
    },
    /// After the image of a letter under one endpoint of a path family ran,
    /// run the other's or splice the transported path between them.
    Conjugated
    {
        /// The path family, closed over its environment.
        motive: crate::arena::ValueClosureId,
        /// The one-letter word transported along.
        along: DomainValueId,
        /// The path transported.
        value: DomainValueId,
        /// Which image the bound value is.
        stage: Conjugating,
    },
    /// After the image of a word's letter under one function of an
    /// endpoint's chain of calls ran, append it and map the next letter.
    Mapping(Mapping),
    /// After the argument a function's case is over evaluated where the
    /// family stands, read the branch it selects as that function's image.
    Selecting(Mapping),
}

/// The state of mapping a word through one endpoint's calls: the routes
/// from each of the binder's occurrences to the endpoint, one after another,
/// each route's functions innermost first.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Mapping
{
    /// The path family, closed over its environment.
    pub motive: crate::arena::ValueClosureId,
    /// The endpoint whose calls map the word.
    pub side: gandr_kernel_term::Side,
    /// The route mapping the word now.
    pub route: Route,
    /// The function of the route mapping the word now.
    pub call: Call,
    /// The word every route maps.
    pub word: DomainValueId,
    /// The images of the routes before this one, concatenated.
    pub routed: DomainValueId,
    /// The letters still to map.
    pub rest: DomainValueId,
    /// The image of the letters mapped so far.
    pub mapped: DomainValueId,
    /// Whether the letter whose image binds next is inverted.
    pub orientation: Orientation,
}

/// A route's position among an endpoint's routes, the binder's leftmost
/// occurrence first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Route(usize);

impl From<usize> for Route
{
    /// The route at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<Route> for usize
{
    /// The route's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(route: Route) -> Self
    {
        route.0
    }
}

/// Which image of a letter a [`CompBody::Conjugated`] continuation binds.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Conjugating
{
    /// The left endpoint's: the right one's is still to run or read.
    Left,
    /// The right endpoint's, after the left one's.
    Right(DomainValueId),
}

/// A function's position in an endpoint's chain of calls, innermost first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Call(usize);

impl From<usize> for Call
{
    /// The function at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<Call> for usize
{
    /// The function's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(call: Call) -> Self
    {
        call.0
    }
}

/// Whether a letter's image is read as written or inverted.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Orientation
{
    /// The letter's own image.
    Forward,
    /// The image of the letter's inverse: the letter's image inverted.
    Inverse,
}

/// A suspended **computation** body with the environment its free variables
/// stand in: what a lambda, a thunk, a bind continuation and a case branch all
/// become.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompClosure
{
    /// The core computation body, unevaluated.
    body: CompBody,
    /// What the body's free variables stand for.
    environment: Environment,
}

impl CompClosure
{
    /// Close `body` over `environment`.
    ///
    /// # Specification
    /// - requires: `environment` binds every occurrence free in `body` in the
    ///   zone that occurrence names; the pairing is the caller's claim.
    /// - ensures: the closure carries exactly the body and environment offered,
    ///   unevaluated.
    /// - provides: the one shape a lambda, a thunk, a bind continuation and a
    ///   case branch all become, which is why the constructor is crate-private.
    /// - fails: never — an environment too shallow for the body surfaces where
    ///   the body is entered, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed and captured lambdas, a forced thunk and two
    ///   successive applications with distinct arguments are observed by their
    ///   source faces and returned value; losing the captured outer binding,
    ///   selecting the inner argument or changing the suspended body changes
    ///   the result.
    /// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
    /// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    #[inline]
    #[must_use]
    #[spec(captures: [intuitionistic = environment.depth(Zone::Intuitionistic), linear = environment.depth(Zone::Linear)], ensures: |ret| ret.body == body && ret.environment.depth(Zone::Intuitionistic) == intuitionistic && ret.environment.depth(Zone::Linear) == linear)]
    pub(crate) fn new(
        body: CompBody,
        environment: Environment,
    ) -> Self
    {
        Self { body, environment }
    }

    /// The suspended body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn body(&self) -> CompBody
    {
        self.body
    }

    /// The captured environment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn environment(&self) -> &Environment
    {
        &self.environment
    }
}

#[cfg(test)]
mod tests;
