//! Junction trees over a factor graph, sum-product over any ordered semiring,
//! and the greatest assignment of a calibrated tree.
//!
//! A junction tree is a tree on cliques of variables in which the cliques
//! that hold a variable are connected: the running intersection property.
//! [`JunctionTree::new`] eliminates the variables in a given order, keeps the
//! maximal cliques that the elimination makes, and joins them by a spanning
//! tree of greatest total separator size, which has the property.
//! [`JunctionTree::with_tree`] takes the cliques and the edges as given and
//! refuses a tree without it, by the variable whose cliques are apart.
//!
//! Sum-product passes Shafer and Shenoy's messages: from each clique toward
//! the first, then back. A message is the semiring sum, onto the separator,
//! of the clique's potential times the messages into the clique from every
//! other edge, so the passes never divide. Each clique's belief is its
//! potential times every message into it. In the probability semiring the
//! beliefs are the marginals of the product of the factors; in the max-times
//! semiring they are its max-marginals. The beliefs make a [`Family`] on the
//! edges of the tree, whose gluing is the certificate of calibration.
//!
//! Each pass is linear in the total size of the clique tables, times the
//! number of edges at a clique, and the size of a clique table is exponential
//! in the treewidth that the order gives.

use alloc::vec;
use alloc::vec::Vec;
use core::iter;

use anodized::spec;
use gandr_theory_cellular_sheaves::CoverIndex;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::OrderedSemiring;

use crate::error::InferenceError;
use crate::factor::FactorGraph;
use crate::glue::Family;
use crate::table::Inclusion;
use crate::table::Projection;
use crate::table::Scope;
use crate::table::Table;
use crate::table::Value;
use crate::table::Variable;

/// An edge of the tree, by its place in the list of edges.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Edge(usize);

/// One edge of a junction tree: its cliques, their separator, and how each
/// clique's entries read as the separator's.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Link
{
    /// The two cliques, as the edge names them.
    ends: (CoverIndex, CoverIndex),
    /// The variables that both cliques hold.
    separator: Scope,
    /// How the first clique's entries read as the separator's.
    from_first: Projection,
    /// How the second clique's entries read as the separator's.
    from_second: Projection,
}

impl Link
{
    /// The clique at the other end from `clique`, and how `clique`'s entries
    /// read as the separator's.
    ///
    /// # Specification
    /// trivial.
    fn side(
        &self,
        clique: CoverIndex,
    ) -> (CoverIndex, &Projection)
    {
        if self.ends.0 == clique {
            (self.ends.1, &self.from_first)
        }
        else {
            (self.ends.0, &self.from_second)
        }
    }
}

/// A clique in the order of a walk from the first, with the edge to the
/// clique before it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Visit
{
    /// The clique.
    clique: CoverIndex,
    /// The edge to its parent, which the walk visits first; none for the
    /// first clique.
    parent: Option<Edge>,
}

/// The messages of one calibration, one each way along each edge.
#[derive(Clone, Debug)]
struct Messages<E>
{
    /// The message from the first clique of each edge to the second.
    toward_second: Vec<Option<Table<E>>>,
    /// The message from the second clique of each edge to the first.
    toward_first: Vec<Option<Table<E>>>,
}

impl<E> Messages<E>
{
    /// The message along `link`, at `place`, that arrives at `clique`.
    ///
    /// # Specification
    /// trivial.
    fn arriving(
        &self,
        link: &Link,
        place: Edge,
        clique: CoverIndex,
    ) -> Option<&Table<E>>
    {
        let side = if link.ends.1 == clique {
            &self.toward_second
        }
        else {
            &self.toward_first
        };
        side.get(place.0)?.as_ref()
    }

    /// Keep `message`, which `clique` sends along `link` at `place`.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        &mut self,
        link: &Link,
        place: Edge,
        clique: CoverIndex,
        message: Table<E>,
    )
    {
        let side = if link.ends.0 == clique {
            &mut self.toward_second
        }
        else {
            &mut self.toward_first
        };
        if let Some(slot) = side.get_mut(place.0) {
            *slot = Some(message);
        }
    }
}

/// The root of `start` in a forest of parent links, where a root is its own
/// parent.
///
/// # Specification
/// trivial.
fn root(
    roots: &[CoverIndex],
    start: CoverIndex,
) -> CoverIndex
{
    let mut at = start;
    while let Some(&next) = roots.get(usize::from(at)) {
        if next == at {
            break;
        }
        at = next;
    }
    at
}

/// Join the variables of `scope` to one another in `neighbours`, but `except`.
///
/// # Specification
/// trivial.
fn link_all(
    neighbours: &mut [Vec<Variable>],
    scope: &Scope,
    except: Option<Variable>,
)
{
    for (first, _) in scope.variables() {
        if Some(first) == except {
            continue;
        }
        let Some(list) = usize::try_from(u32::from(first))
            .ok()
            .and_then(|place| neighbours.get_mut(place))
        else {
            continue;
        };
        for (second, _) in scope.variables() {
            if second == first || Some(second) == except {
                continue;
            }
            if let Err(place) = list.binary_search(&second) {
                list.insert(place, second);
            }
        }
    }
}

/// The cliques of a tree in the order of a walk from the first, each with the
/// edge it is reached by.
///
/// # Specification
/// trivial.
fn walk(
    links: &[Link],
    incident: &[Vec<Edge>],
    count: Width,
) -> Vec<Visit>
{
    let mut seen = vec![false; usize::from(count)];
    let mut walk = Vec::with_capacity(usize::from(count));
    if let Some(first) = seen.first_mut() {
        *first = true;
        walk.push(Visit {
            clique: CoverIndex::from(0_usize),
            parent: None,
        });
    }
    let mut next = 0_usize;
    while let Some(&visit) = walk.get(next) {
        next = next.saturating_add(1);
        for &place in incident
            .get(usize::from(visit.clique))
            .into_iter()
            .flatten()
        {
            let Some(link) = links.get(place.0)
            else {
                continue;
            };
            let (other, _) = link.side(visit.clique);
            if let Some(mark) = seen.get_mut(usize::from(other))
                && !*mark
            {
                *mark = true;
                walk.push(Visit {
                    clique: other,
                    parent: Some(place),
                });
            }
        }
    }
    walk
}

/// The entry of `belief` of greatest weight in `semiring`'s order, the first
/// of them, among the entries that restrict to `fixed`'s separator entry.
///
/// # Specification
/// trivial.
fn greatest<E, S>(
    semiring: &S,
    belief: &Table<E>,
    fixed: Option<(Entry, &Projection)>,
) -> Result<Entry, InferenceError>
where
    S: OrderedSemiring<Element = E>,
{
    belief
        .weights()
        .iter()
        .enumerate()
        .filter(|&(entry, _)| {
            fixed.is_none_or(|(separator, projection)| {
                projection.entry(Entry::from(entry)) == Some(separator)
            })
        })
        .fold(
            None,
            |best: Option<(usize, &E)>, (entry, weight)| match best {
                Some((_, kept)) if semiring.compare(weight, kept) == Comparison::Below => best,
                _ => Some((entry, weight)),
            },
        )
        .map(|(entry, _)| Entry::from(entry))
        .ok_or(InferenceError::Uncovered)
}

/// A tree on cliques of variables with the running intersection property,
/// with the separator of each edge.
///
/// # Specification
/// - ensures: the edges make one tree on the cliques, and the cliques that hold
///   any one variable are connected in it.
/// - provides: the cliques, sum-product over a semiring, and the greatest
///   assignment of a calibrated tree.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`JunctionTree::with_tree`]'s.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JunctionTree
{
    /// The cliques.
    cliques: Vec<Scope>,
    /// The edges, with their separators.
    links: Vec<Link>,
    /// The edges at each clique.
    incident: Vec<Vec<Edge>>,
    /// The cliques in the order of a walk from the first.
    walk: Vec<Visit>,
    /// One more than the greatest number of a variable that a clique holds:
    /// the slots of a decoded assignment.
    span: Width,
}

impl JunctionTree
{
    /// The tree that eliminating the variables of `graph` in `order` gives.
    ///
    /// # Specification
    /// - ensures: a junction tree whose cliques are the maximal cliques of the
    ///   elimination, so each factor's scope lies within a clique.
    /// - fails: an order that names a variable the graph does not hold, names
    ///   one twice, or leaves one out is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Unknown`]: the order names a variable the graph does
    ///   not hold.
    /// - [`InferenceError::Repeated`]: the order names a variable twice.
    /// - [`InferenceError::NotEliminated`]: the order leaves a variable out.
    /// - [`InferenceError::NotATree`]: the graph holds no variable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the network's order gives its two cliques of three; a
    ///   chain of sixteen gives fifteen cliques of two; an order that leaves a
    ///   variable out, or names one twice, is refused by it.
    /// - witness: `tests::inference::sum_product_gives_the_marginals_of_the_network`
    /// - witness: `tests::inference::a_chain_of_sixteen_marginalises_and_decodes`
    /// - witness: `tests::inference::a_tree_without_running_intersection_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |tree| graph.factors().iter().all(|factor| tree.cliques.iter().any(|clique| factor.scope().inclusion(clique) == Inclusion::Within))))]
    #[inline]
    pub fn new<E>(
        graph: &FactorGraph<E>,
        order: &[Variable],
    ) -> Result<Self, InferenceError>
    {
        let count = graph.arities().len();
        let mut neighbours: Vec<Vec<Variable>> = vec![Vec::new(); count];
        for factor in graph.factors() {
            link_all(&mut neighbours, factor.scope(), None);
        }
        let mut eliminated = vec![false; count];
        let mut cliques: Vec<Scope> = Vec::with_capacity(order.len());
        for &variable in order {
            let place = usize::try_from(u32::from(variable))
                .ok()
                .filter(|&place| place < count)
                .ok_or(InferenceError::Unknown(variable))?;
            let done = eliminated
                .get_mut(place)
                .ok_or(InferenceError::Unknown(variable))?;
            if *done {
                return Err(InferenceError::Repeated(variable));
            }
            *done = true;
            let members = neighbours
                .get(place)
                .into_iter()
                .flatten()
                .copied()
                .filter(|neighbour| {
                    usize::try_from(u32::from(*neighbour))
                        .ok()
                        .and_then(|at| eliminated.get(at))
                        .is_some_and(|gone| !*gone)
                })
                .chain(iter::once(variable))
                .map(|member| {
                    graph
                        .arity(member)
                        .map(|arity| (member, arity))
                        .ok_or(InferenceError::Unknown(member))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let clique = Scope::new(members)?;
            link_all(&mut neighbours, &clique, Some(variable));
            cliques.push(clique);
        }
        if let Some(missing) = eliminated.iter().position(|done| !*done) {
            let number = u32::try_from(missing).map_err(|_past| InferenceError::TooLarge)?;
            return Err(InferenceError::NotEliminated(Variable::from(number)));
        }
        // A clique holds no variable eliminated before it, so it lies within
        // no clique made after it: it is maximal when it lies within none
        // made before it.
        let maximal: Vec<Scope> = cliques
            .iter()
            .enumerate()
            .filter(|&(place, clique)| {
                cliques
                    .iter()
                    .take(place)
                    .all(|earlier| clique.inclusion(earlier) == Inclusion::Beyond)
            })
            .map(|(_, clique)| clique.clone())
            .collect();
        let size = maximal.len();
        let mut pairs: Vec<(Width, CoverIndex, CoverIndex)> = (0 .. size)
            .flat_map(|first| (first .. size).skip(1).map(move |second| (first, second)))
            .filter_map(|(first, second)| {
                let shared = maximal.get(first)?.shared(maximal.get(second)?);
                Some((shared, CoverIndex::from(first), CoverIndex::from(second)))
            })
            .collect();
        pairs.sort_by_key(|pair| core::cmp::Reverse(pair.0));
        let mut roots: Vec<CoverIndex> = (0 .. size).map(CoverIndex::from).collect();
        let mut edges = Vec::with_capacity(size.saturating_sub(1));
        for &(_, first, second) in &pairs {
            let (one, other) = (root(&roots, first), root(&roots, second));
            if one != other {
                if let Some(slot) = roots.get_mut(usize::from(one)) {
                    *slot = other;
                }
                edges.push((first, second));
            }
        }
        Self::with_tree(maximal, &edges)
    }

    /// The tree on `cliques` whose edges `edges` lists.
    ///
    /// # Specification
    /// - ensures: the tree holds the cliques and the edges in order, with the
    ///   separator of each edge.
    /// - fails: edges that do not make one tree, an edge past the cliques, a
    ///   variable with two arities, and a variable whose cliques are apart are
    ///   each refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::NotATree`]: the edges are not one fewer than the
    ///   cliques, or they close a cycle.
    /// - [`InferenceError::NoMember`]: an edge names a clique past the list.
    /// - [`InferenceError::Mismatched`]: two cliques give a variable two
    ///   arities.
    /// - [`InferenceError::RunningIntersection`]: the cliques that hold the
    ///   variable are not connected.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the path of the contextual family's three scopes is
    ///   refused by the variable at its two ends; a cycle and a missing edge
    ///   are refused as no tree.
    /// - witness: `tests::inference::a_tree_without_running_intersection_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |tree| tree.links.len().checked_add(1) == Some(tree.cliques.len()) && tree.walk.len() == tree.cliques.len()))]
    #[inline]
    pub fn with_tree(
        cliques: Vec<Scope>,
        edges: &[(CoverIndex, CoverIndex)],
    ) -> Result<Self, InferenceError>
    {
        let count = cliques.len();
        if count.checked_sub(1) != Some(edges.len()) {
            return Err(InferenceError::NotATree);
        }
        let mut roots: Vec<CoverIndex> = (0 .. count).map(CoverIndex::from).collect();
        for &(first, second) in edges {
            if let Some(&past) = [first, second]
                .iter()
                .find(|end| usize::from(**end) >= count)
            {
                return Err(InferenceError::NoMember(past));
            }
            let (one, other) = (root(&roots, first), root(&roots, second));
            if one == other {
                return Err(InferenceError::NotATree);
            }
            if let Some(slot) = roots.get_mut(usize::from(one)) {
                *slot = other;
            }
        }
        let mut variables: Vec<Variable> = cliques
            .iter()
            .flat_map(|clique| clique.variables().map(|(variable, _)| variable))
            .collect();
        variables.sort_unstable();
        variables.dedup();
        for &variable in &variables {
            let holds = |end: CoverIndex| {
                cliques
                    .get(usize::from(end))
                    .and_then(|clique| clique.holds(variable))
                    .is_some()
            };
            let holders = (0 .. count)
                .map(CoverIndex::from)
                .filter(|&clique| holds(clique))
                .count();
            let linked = edges
                .iter()
                .filter(|&&(first, second)| holds(first) && holds(second))
                .count();
            if linked.checked_add(1) != Some(holders) {
                return Err(InferenceError::RunningIntersection(variable));
            }
        }
        let links = edges
            .iter()
            .map(|&(first, second)| {
                let one = cliques
                    .get(usize::from(first))
                    .ok_or(InferenceError::NoMember(first))?;
                let other = cliques
                    .get(usize::from(second))
                    .ok_or(InferenceError::NoMember(second))?;
                let separator = one.meet(other)?;
                let from_first = one
                    .projection(&separator)
                    .ok_or(InferenceError::Uncovered)?;
                let from_second = other
                    .projection(&separator)
                    .ok_or(InferenceError::Uncovered)?;
                Ok(Link {
                    ends: (first, second),
                    separator,
                    from_first,
                    from_second,
                })
            })
            .collect::<Result<Vec<_>, InferenceError>>()?;
        let mut incident: Vec<Vec<Edge>> = vec![Vec::new(); count];
        for (place, link) in links.iter().enumerate() {
            for end in <[CoverIndex; 2]>::from(link.ends) {
                if let Some(list) = incident.get_mut(usize::from(end)) {
                    list.push(Edge(place));
                }
            }
        }
        let walk = walk(&links, &incident, Width::from(count));
        let span = cliques
            .iter()
            .flat_map(Scope::variables)
            .map(|(variable, _)| u32::from(variable))
            .max()
            .map_or(Ok(0_usize), |last| {
                usize::try_from(last)
                    .ok()
                    .and_then(|last| last.checked_add(1))
                    .ok_or(InferenceError::TooLarge)
            })?;
        Ok(Self {
            cliques,
            links,
            incident,
            walk,
            span: Width::from(span),
        })
    }

    /// The cliques.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cliques(&self) -> &[Scope]
    {
        &self.cliques
    }

    /// The edges, each by its two cliques.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn edges(&self) -> impl Iterator<Item = (CoverIndex, CoverIndex)> + '_
    {
        self.links.iter().map(|link| link.ends)
    }

    /// The beliefs of the cliques after sum-product over `semiring`: each
    /// factor of `graph` multiplies into the first clique that holds its
    /// scope, and one pass of messages runs toward the first clique and one
    /// back.
    ///
    /// # Specification
    /// - ensures: each clique's belief is the semiring sum, over the variables
    ///   it does not hold, of the product of every factor: the marginal in the
    ///   probability semiring and the max-marginal in the max-times semiring.
    ///   The beliefs are a family on the tree's edges.
    /// - fails: a factor whose scope lies within no clique, and a sum or a
    ///   product past the carrier, are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Uncovered`]: a factor's scope lies within no clique.
    /// - [`InferenceError::Overflow`]: a sum or a product passes the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each clique and separator marginal of the network
    ///   against the sum over its sixteen worlds; each marginal of the chain of
    ///   sixteen against the sum over its 65 536 assignments.
    /// - witness: `tests::inference::sum_product_gives_the_marginals_of_the_network`
    /// - witness: `tests::inference::a_chain_of_sixteen_marginalises_and_decodes`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |calibrated| calibrated.family.members().len() == self.cliques.len()))]
    #[inline]
    pub fn calibrate<S>(
        &self,
        semiring: &S,
        graph: &FactorGraph<S::Element>,
    ) -> Result<Calibrated<S::Element>, InferenceError>
    where
        S: OrderedSemiring,
    {
        let one = semiring.one();
        let mut potentials: Vec<Table<S::Element>> = self
            .cliques
            .iter()
            .map(|clique| Table::filled(clique.clone(), &one))
            .collect();
        for factor in graph.factors() {
            let potential = potentials
                .iter_mut()
                .find(|potential| factor.scope().inclusion(potential.scope()) == Inclusion::Within)
                .ok_or(InferenceError::Uncovered)?;
            potential.multiply_by(semiring, factor)?;
        }
        let mut messages = Messages {
            toward_second: vec![None; self.links.len()],
            toward_first: vec![None; self.links.len()],
        };
        for visit in self.walk.iter().rev() {
            if let Some(place) = visit.parent {
                let message = self.send(semiring, &potentials, &messages, visit.clique, place)?;
                let link = self.links.get(place.0).ok_or(InferenceError::NotATree)?;
                messages.keep(link, place, visit.clique, message);
            }
        }
        for visit in &self.walk {
            for &place in self
                .incident
                .get(usize::from(visit.clique))
                .into_iter()
                .flatten()
            {
                if Some(place) == visit.parent {
                    continue;
                }
                let message = self.send(semiring, &potentials, &messages, visit.clique, place)?;
                let link = self.links.get(place.0).ok_or(InferenceError::NotATree)?;
                messages.keep(link, place, visit.clique, message);
            }
        }
        for (place, potential) in potentials.iter_mut().enumerate() {
            let clique = CoverIndex::from(place);
            for (entry, weight) in potential.weights_mut().iter_mut().enumerate() {
                *weight = self.incoming(
                    semiring,
                    &messages,
                    clique,
                    Entry::from(entry),
                    None,
                    weight,
                )?;
            }
        }
        let edges = self.links.iter().map(|link| link.ends).collect();
        Ok(Calibrated {
            family: Family::new(potentials, edges)?,
        })
    }

    /// The message that `clique` sends along the edge at `through`: the sum,
    /// onto the separator, of the clique's potential times every message into
    /// it from its other edges.
    ///
    /// # Specification
    /// trivial.
    fn send<S>(
        &self,
        semiring: &S,
        potentials: &[Table<S::Element>],
        messages: &Messages<S::Element>,
        clique: CoverIndex,
        through: Edge,
    ) -> Result<Table<S::Element>, InferenceError>
    where
        S: OrderedSemiring,
    {
        let link = self.links.get(through.0).ok_or(InferenceError::NotATree)?;
        let potential = potentials
            .get(usize::from(clique))
            .ok_or(InferenceError::NoMember(clique))?;
        let (_, onto) = link.side(clique);
        let mut weights = vec![semiring.zero(); usize::from(link.separator.width())];
        for (entry, weight) in potential.weights().iter().enumerate() {
            let entry = Entry::from(entry);
            let value = self.incoming(semiring, messages, clique, entry, Some(through), weight)?;
            let target = onto.entry(entry).ok_or(InferenceError::TooLarge)?;
            let slot = weights
                .get_mut(usize::from(target))
                .ok_or(InferenceError::TooLarge)?;
            *slot = semiring
                .add(slot, &value)
                .map_err(|_outside| InferenceError::Overflow)?;
        }
        Table::new(link.separator.clone(), weights)
    }

    /// `weight` times the message into `clique` along each of its edges but
    /// `except`, each read at the separator entry that `entry` restricts to.
    ///
    /// # Specification
    /// trivial.
    fn incoming<S>(
        &self,
        semiring: &S,
        messages: &Messages<S::Element>,
        clique: CoverIndex,
        entry: Entry,
        except: Option<Edge>,
        weight: &S::Element,
    ) -> Result<S::Element, InferenceError>
    where
        S: OrderedSemiring,
    {
        self.incident
            .get(usize::from(clique))
            .into_iter()
            .flatten()
            .filter(|&&place| Some(place) != except)
            .try_fold(weight.clone(), |value, &place| {
                let link = self.links.get(place.0).ok_or(InferenceError::NotATree)?;
                let (_, projection) = link.side(clique);
                let message = messages
                    .arriving(link, place, clique)
                    .ok_or(InferenceError::Uncovered)?;
                let at = projection.entry(entry).ok_or(InferenceError::TooLarge)?;
                let by = message.at(at).ok_or(InferenceError::TooLarge)?;
                semiring
                    .multiply(&value, by)
                    .map_err(|_outside| InferenceError::Overflow)
            })
    }

    /// The assignment of greatest weight that `calibrated`'s beliefs give:
    /// the first clique's entry of greatest weight, then, along the walk,
    /// each clique's entry of greatest weight among those that agree with
    /// its parent on their separator.
    ///
    /// # Specification
    /// - ensures: one slot for each variable number up to the greatest that a
    ///   clique holds, and a value for each variable of the cliques. When
    ///   `semiring`'s sum takes the greater of two weights, as max-times does,
    ///   and `calibrated` is this tree's calibration over it, the assignment
    ///   has the greatest product of the factors.
    /// - fails: beliefs that are not one table for each clique are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::NoMember`]: the beliefs hold fewer tables than the
    ///   tree has cliques.
    /// - [`InferenceError::Uncovered`]: a belief has no entry that agrees with
    ///   its parent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the network's most likely world and the chain's most
    ///   likely assignment, each against the greatest joint weight over every
    ///   world.
    /// - witness: `tests::inference::max_times_gives_the_most_likely_world_of_the_network`
    /// - witness: `tests::inference::a_chain_of_sixteen_marginalises_and_decodes`
    #[spec(ensures: |ref ret| ret.as_ref().ok().is_none_or(|assignment| assignment.values.len() == usize::from(self.span)))]
    #[inline]
    pub fn decode<S>(
        &self,
        semiring: &S,
        calibrated: &Calibrated<S::Element>,
    ) -> Result<Assignment, InferenceError>
    where
        S: OrderedSemiring,
    {
        let beliefs = calibrated.family.members();
        let mut chosen: Vec<Option<Entry>> = vec![None; self.cliques.len()];
        for visit in &self.walk {
            let belief = beliefs
                .get(usize::from(visit.clique))
                .ok_or(InferenceError::NoMember(visit.clique))?;
            let fixed = match visit.parent {
                None => None,
                Some(place) => {
                    let link = self.links.get(place.0).ok_or(InferenceError::NotATree)?;
                    let (parent, mine) = link.side(visit.clique);
                    let (_, theirs) = link.side(parent);
                    let kept = chosen
                        .get(usize::from(parent))
                        .copied()
                        .flatten()
                        .ok_or(InferenceError::Uncovered)?;
                    Some((theirs.entry(kept).ok_or(InferenceError::TooLarge)?, mine))
                },
            };
            let best = greatest(semiring, belief, fixed)?;
            if let Some(slot) = chosen.get_mut(usize::from(visit.clique)) {
                *slot = Some(best);
            }
        }
        let mut values: Vec<Option<Value>> = vec![None; usize::from(self.span)];
        for (clique, entry) in self.cliques.iter().zip(&chosen) {
            let Some(entry) = *entry
            else {
                continue;
            };
            for (variable, _) in clique.variables() {
                if let Some(slot) = usize::try_from(u32::from(variable))
                    .ok()
                    .and_then(|place| values.get_mut(place))
                {
                    *slot = clique.value(entry, variable);
                }
            }
        }
        Ok(Assignment { values })
    }
}

/// The beliefs of the cliques of a calibrated tree, as a family on its edges.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Calibrated<E>
{
    /// The beliefs, one for each clique, with the tree's edges as overlaps.
    family: Family<E>,
}

impl<E> Calibrated<E>
{
    /// The beliefs, one for each clique, with the tree's edges as overlaps:
    /// [`Family::glue`] gives the separators and certifies calibration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn family(&self) -> &Family<E>
    {
        &self.family
    }
}

impl<E: Clone> Calibrated<E>
{
    /// The marginal on `onto` that the first clique holding it gives.
    ///
    /// # Specification
    /// - ensures: the semiring sum of the first such clique's belief over the
    ///   variables that `onto` does not hold.
    /// - fails: a scope that lies within no clique, and a sum past the carrier,
    ///   are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`InferenceError::Uncovered`]: `onto` lies within no clique.
    /// - [`InferenceError::Overflow`]: a sum passes the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the marginal of each variable of the network against
    ///   the sum over its worlds.
    /// - witness: `tests::inference::sum_product_gives_the_marginals_of_the_network`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |table| table.scope() == onto))]
    #[inline]
    pub fn marginal<S>(
        &self,
        semiring: &S,
        onto: &Scope,
    ) -> Result<Table<E>, InferenceError>
    where
        S: OrderedSemiring<Element = E>,
    {
        self.family
            .members()
            .iter()
            .find(|belief| onto.inclusion(belief.scope()) == Inclusion::Within)
            .ok_or(InferenceError::Uncovered)?
            .marginal(semiring, onto)
    }
}

/// A value for each variable of a tree's cliques.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Assignment
{
    /// The value of each variable, by its number; none for a number that no
    /// clique holds.
    values: Vec<Option<Value>>,
}

impl Assignment
{
    /// The value of `variable`, when a clique holds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        variable: Variable,
    ) -> Option<Value>
    {
        usize::try_from(u32::from(variable))
            .ok()
            .and_then(|place| self.values.get(place))
            .copied()
            .flatten()
    }
}
