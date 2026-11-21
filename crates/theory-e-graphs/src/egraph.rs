//! The e-graph: classes over the places of a term table, the parents of each
//! class, the proof forest and the worklist rebuild.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::mem;

use gandr_theory_coherent_resolutions::Arity;
use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Variable;

use crate::analysis::Analysis;
use crate::analysis::Growth;
use crate::error::EGraphError;

mod explain;
mod saturate;

pub use self::explain::Explanation;
pub use self::explain::Position;
pub use self::explain::Proof;
pub use self::explain::ProofPlace;
pub use self::explain::Refusal;
pub use self::explain::Step;
pub use self::explain::StepPlace;
pub use self::explain::StepReason;
pub use self::saturate::Budget;
pub use self::saturate::Outcome;
pub use self::saturate::Run;

/// The leader of a place that the e-graph does not hold.
const ABSENT: usize = usize::MAX;

wrapper! {
    /// The place of an equation among the e-graph's equations, in the order
    /// of their statement.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct EquationPlace(usize);
}

wrapper! {
    /// A count: of unions, of repairs, of nodes, of rounds or of matches.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Count(usize);
}

/// An input equation: two terms of the table. The variables of the equation
/// take their places by their first occurrence on the left, as the rules of a
/// Lawvere theory do.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Equation
{
    /// The left side: the pattern that a match reads.
    pub left: TermPlace,
    /// The right side.
    pub right: TermPlace,
    /// The number of variables, each of the left side.
    pub variables: Arity,
}

/// The side of an equation that a step starts from.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Direction
{
    /// From the left side to the right side.
    Forward,
    /// From the right side to the left side.
    Backward,
}

impl Direction
{
    /// The other direction.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flipped(self) -> Self
    {
        match self {
            Self::Forward => Self::Backward,
            Self::Backward => Self::Forward,
        }
    }
}

/// Why two nodes are equal.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Reason
{
    /// An input equation at an instance. The first node is the side of the
    /// equation that `direction` starts from, with each variable `x` replaced
    /// by `values[x]`; the second node is the other side, under the same
    /// values.
    Input
    {
        /// The equation.
        equation: EquationPlace,
        /// The side that the first node is an instance of.
        direction: Direction,
        /// The value of each variable, by its place.
        values: Vec<TermPlace>,
    },
    /// A congruence: the two nodes have one head, and their children are
    /// equal place by place.
    Congruence,
}

impl Reason
{
    /// The reason read from the second node to the first.
    ///
    /// # Specification
    /// trivial.
    fn flip(&mut self)
    {
        if let Self::Input {
            ref mut direction, ..
        } = *self
        {
            *direction = direction.flipped();
        }
    }
}

/// A union of two nodes that one class already holds, with its reason: a
/// loop of the class.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Redundant
{
    /// The first node.
    pub left: TermPlace,
    /// The second node.
    pub right: TermPlace,
    /// Why the two are equal a second time.
    pub reason: Reason,
}

/// Whether a union merges two classes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Joined
{
    /// The two nodes lay in two classes, and the union merges them.
    Merged,
    /// One class held the two nodes, so the union is [`Redundant`].
    Already,
}

/// What the e-graph has done so far.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Tally
{
    /// The unions that merge two classes.
    pub unions: Count,
    /// The unions inside one class.
    pub redundant: Count,
    /// The repairs of a class that the rebuild runs.
    pub repairs: Count,
    /// The nodes that the e-graph holds.
    pub nodes: Count,
}

/// An edge of the proof forest: the neighbour, and the place of the reason
/// read from this node to the neighbour.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Edge
{
    /// The neighbour.
    to: usize,
    /// The place of the reason.
    reason: usize,
}

/// A parent with its signature: its head, and its children's classes as a
/// run of the repair's class buffer.
#[derive(Clone, Copy, Debug)]
struct Key
{
    /// The head.
    head: TermHead,
    /// The first child class in the buffer.
    start: usize,
    /// One past the last child class in the buffer.
    end: usize,
    /// The parent.
    parent: TermPlace,
}

/// The buffers of a repair, kept from one repair to the next so that a
/// repair allocates nothing once they are large enough.
#[derive(Clone, Debug, Default)]
struct Scratch
{
    /// The signature of each parent.
    keys: Vec<Key>,
    /// The children's classes of each parent, one run for each key.
    classes: Vec<TermPlace>,
    /// The congruent pairs: the parent that stays, and the parent that joins
    /// it.
    joins: Vec<(TermPlace, TermPlace)>,
    /// The parents that stay in the class's list.
    kept: Vec<TermPlace>,
}

/// Whether a walk enters a term or leaves it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Hold the children first.
    Enter,
    /// Hold the term, its children held.
    Leave,
}

/// Whether a congruent parent stands for a node in its children's parent
/// lists.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// The node stands for its signature.
    Live,
    /// A congruent node of its class stands for it, so a repair skips it.
    Retired,
}

/// A congruence closure over the terms of a [`TermTable`], with a proof
/// forest, a worklist rebuild and an [`Analysis`].
///
/// The nodes are the table's places: the e-graph holds a place, with each of
/// its arguments, once a caller adds it or a match builds it. Each class has
/// a root, a cycle through its members, a list of its parents and a datum.
/// Each node has at most one edge of the proof forest.
#[derive(Clone, Debug)]
pub struct EGraph<A = ()>
where
    A: Analysis,
{
    /// The terms. A place keeps its term, so a class never changes under a
    /// new term.
    table: TermTable,
    /// The input equations, by place.
    equations: Vec<Equation>,
    /// The analysis.
    analysis: A,
    /// The leader of each place in the union-find, the place itself at a
    /// root, or [`ABSENT`].
    leader: Vec<usize>,
    /// The number of members of each class, at its root.
    members: Vec<usize>,
    /// The next member of each place's class, round a cycle.
    next: Vec<usize>,
    /// The parents of each class, at its root, each at least once.
    uses: Vec<Vec<TermPlace>>,
    /// The datum of each class, at its root.
    data: Vec<Option<A::Data>>,
    /// The proof-forest edge of each place.
    proof: Vec<Option<Edge>>,
    /// The reason of each proof-forest edge, by place.
    reasons: Vec<Reason>,
    /// Whether each place stands for its signature.
    standing: Vec<Standing>,
    /// The unions inside one class, in their order.
    redundant: Vec<Redundant>,
    /// The classes whose parents a rebuild repairs.
    worklist: Vec<TermPlace>,
    /// The classes of one chunk of the rebuild, kept from one rebuild to the
    /// next.
    todo: Vec<TermPlace>,
    /// The instances that the e-graph applies, each once.
    applied: BTreeSet<(EquationPlace, Vec<TermPlace>)>,
    /// The repair's buffers.
    scratch: Scratch,
    /// The unions that merge two classes.
    unions: usize,
    /// The repairs that the rebuild runs.
    repairs: usize,
    /// The nodes held.
    nodes: usize,
}

/// The members of one class, round its cycle.
#[derive(Clone, Debug)]
pub struct Members<'graph>
{
    /// The next member of each place.
    next: &'graph [usize],
    /// The member the walk starts from.
    start: usize,
    /// The member the walk gives next.
    at: Option<usize>,
}

impl Iterator for Members<'_>
{
    type Item = TermPlace;

    /// The next member, until the cycle closes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<TermPlace>
    {
        let at = self.at?;
        self.at = self
            .next
            .get(at)
            .copied()
            .filter(|&next| next != self.start && next != ABSENT);
        Some(TermPlace::from(at))
    }
}

/// The classes of an e-graph, each by its root, in the order of the roots.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Classes<'graph>
{
    /// The leaders, with their places.
    leaders: core::iter::Enumerate<core::slice::Iter<'graph, usize>>,
}

impl Iterator for Classes<'_>
{
    type Item = TermPlace;

    /// The next root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<TermPlace>
    {
        self.leaders
            .find(|&(place, &leader)| place == leader)
            .map(|(place, _)| TermPlace::from(place))
    }
}

/// The data of a node's children's classes, in the order of the arguments.
struct ChildData<'graph, D>
{
    /// The children's roots.
    roots: core::slice::Iter<'graph, TermPlace>,
    /// The data, by root.
    data: &'graph [Option<D>],
}

impl<'graph, D> Iterator for ChildData<'graph, D>
{
    type Item = &'graph D;

    /// The datum of the next child's class. The caller checks first that
    /// each root holds a datum.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<&'graph D>
    {
        let &root = self.roots.next()?;
        self.data.get(usize::from(root)).and_then(Option::as_ref)
    }

    /// The children left.
    ///
    /// # Specification
    /// trivial.
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        self.roots.size_hint()
    }
}

impl<D> ExactSizeIterator for ChildData<'_, D>
{
}

impl<A> EGraph<A>
where
    A: Analysis,
{
    /// An e-graph over `table` that holds no term yet, with `analysis`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        table: TermTable,
        analysis: A,
    ) -> Self
    {
        Self {
            table,
            equations: Vec::new(),
            analysis,
            leader: Vec::new(),
            members: Vec::new(),
            next: Vec::new(),
            uses: Vec::new(),
            data: Vec::new(),
            proof: Vec::new(),
            reasons: Vec::new(),
            standing: Vec::new(),
            redundant: Vec::new(),
            worklist: Vec::new(),
            todo: Vec::new(),
            applied: BTreeSet::new(),
            scratch: Scratch {
                keys: Vec::new(),
                classes: Vec::new(),
                joins: Vec::new(),
                kept: Vec::new(),
            },
            unions: 0,
            repairs: 0,
            nodes: 0,
        }
    }

    /// The terms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn table(&self) -> &TermTable
    {
        &self.table
    }

    /// The terms, to intern more. A place keeps its term, so the classes stay
    /// true.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn table_mut(&mut self) -> &mut TermTable
    {
        &mut self.table
    }

    /// The analysis.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn analysis(&self) -> &A
    {
        &self.analysis
    }

    /// The input equations, by place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn equations(&self) -> &[Equation]
    {
        &self.equations
    }

    /// The unions inside one class, in their order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn redundant(&self) -> &[Redundant]
    {
        &self.redundant
    }

    /// What the e-graph has done so far.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tally(&self) -> Tally
    {
        Tally {
            unions: Count::from(self.unions),
            redundant: Count::from(self.redundant.len()),
            repairs: Count::from(self.repairs),
            nodes: Count::from(self.nodes),
        }
    }

    /// State the equation `left = right` over the table's terms.
    ///
    /// # Specification
    /// - ensures: the equation takes the next place, and its variables are the
    ///   variables of its left side.
    /// - fails: [`EGraphError::VariableLeft`] when the left side is a variable;
    ///   [`EGraphError::Unbound`] with the first variable of the right side
    ///   that the left side lacks; [`EGraphError::Values`] when the variables
    ///   of the left side skip a place; [`EGraphError::Table`] when a side is
    ///   not in the table.
    /// - panics: none.
    /// - executable: none — the ensures reads the variables of two terms, and
    ///   the call holds no second reading to compare.
    ///
    /// # Errors
    /// - [`EGraphError::VariableLeft`]: the left side matches every term.
    /// - [`EGraphError::Unbound`]: the right side holds a variable that the
    ///   left side lacks.
    /// - [`EGraphError::Values`]: the left side's variables skip a place.
    /// - [`EGraphError::Table`]: a side is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a variable left side, a right side with a new
    ///   variable, and a ground equation separate the three outcomes.
    /// - witness: `tests::graph::an_equation_that_cannot_match_is_refused_by_name`
    #[inline]
    pub fn equation(
        &mut self,
        left: TermPlace,
        right: TermPlace,
    ) -> Result<EquationPlace, EGraphError>
    {
        let place = EquationPlace::from(self.equations.len());
        if let TermHead::Var(_) = self.table.node(left)?.head {
            return Err(EGraphError::VariableLeft(place));
        }
        let left_variables = self.variables(left)?;
        let right_variables = self.variables(right)?;
        if let Some(&unbound) = right_variables.difference(&left_variables).next() {
            return Err(EGraphError::Unbound(place, unbound));
        }
        let count = left_variables.len();
        if left_variables
            .last()
            .is_some_and(|&last| usize::from(last) >= count)
        {
            return Err(EGraphError::Values(place));
        }
        self.equations.push(Equation {
            left,
            right,
            variables: Arity::from(count),
        });
        Ok(place)
    }

    /// The variables of the term at `place`.
    ///
    /// # Specification
    /// trivial.
    fn variables(
        &self,
        place: TermPlace,
    ) -> Result<BTreeSet<Variable>, EGraphError>
    {
        let mut found = BTreeSet::new();
        let mut pending = vec![place];
        while let Some(next) = pending.pop() {
            let node = self.table.node(next)?;
            match node.head {
                TermHead::Var(variable) => {
                    let _new = found.insert(variable);
                },
                TermHead::Op(_) => pending.extend(node.children.iter().copied()),
            }
        }
        Ok(found)
    }

    /// The leader of `at`, or none for a place that the e-graph does not hold.
    ///
    /// # Specification
    /// trivial.
    fn leader(
        &self,
        at: TermPlace,
    ) -> Option<TermPlace>
    {
        self.leader
            .get(usize::from(at))
            .copied()
            .filter(|&leader| leader != ABSENT)
            .map(TermPlace::from)
    }

    /// The root of the class of `at`, read without a change.
    ///
    /// # Specification
    /// trivial.
    fn root(
        &self,
        at: TermPlace,
    ) -> Result<TermPlace, EGraphError>
    {
        let mut here = at;
        loop {
            let up = self.leader(here).ok_or(EGraphError::Unheld(at))?;
            if up == here {
                return Ok(here);
            }
            here = up;
        }
    }

    /// The root of the class of `at`, each place on the way pointed at the
    /// root.
    ///
    /// # Specification
    /// trivial.
    fn compress(
        &mut self,
        at: TermPlace,
    ) -> Result<TermPlace, EGraphError>
    {
        let root = self.root(at)?;
        let mut here = at;
        while here != root {
            let up = self.leader(here).ok_or(EGraphError::Unheld(at))?;
            if let Some(slot) = self.leader.get_mut(usize::from(here)) {
                *slot = usize::from(root);
            }
            here = up;
        }
        Ok(root)
    }

    /// The root of the class of the term at `place`.
    ///
    /// # Specification
    /// - ensures: two places give one root exactly when one class holds them.
    /// - fails: [`EGraphError::Unheld`] when the e-graph does not hold the
    ///   term.
    /// - panics: none.
    /// - executable: none — the ensures is a statement about every two places,
    ///   and the call reads one.
    ///
    /// # Errors
    /// - [`EGraphError::Unheld`]: the e-graph does not hold the term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two terms joined by an equation and a third term
    ///   apart from them separate the two outcomes.
    /// - witness: `tests::graph::a_term_is_held_with_each_argument_once`
    #[inline]
    pub fn find(
        &self,
        place: TermPlace,
    ) -> Result<TermPlace, EGraphError>
    {
        self.root(place)
    }

    /// The members of the class of the term at `place`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`EGraphError::Unheld`]: the e-graph does not hold the term.
    #[inline]
    pub fn members(
        &self,
        place: TermPlace,
    ) -> Result<Members<'_>, EGraphError>
    {
        let start = usize::from(self.root(place)?);
        Ok(Members {
            next: &self.next,
            start,
            at: Some(start),
        })
    }

    /// The classes, each by its root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn classes(&self) -> Classes<'_>
    {
        Classes {
            leaders: self.leader.iter().enumerate(),
        }
    }

    /// The datum of the class of the term at `place`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`EGraphError::Unheld`]: the e-graph does not hold the term.
    #[inline]
    pub fn data(
        &self,
        place: TermPlace,
    ) -> Result<&A::Data, EGraphError>
    {
        let root = usize::from(self.root(place)?);
        self.data
            .get(root)
            .and_then(Option::as_ref)
            .ok_or(EGraphError::Unheld(place))
    }

    /// Hold the term at `place`, with each of its arguments, and give the
    /// root of its class.
    ///
    /// # Specification
    /// - ensures: the e-graph holds the term and each of its arguments, each in
    ///   a class of its own when it is new. A new term whose children's classes
    ///   make it congruent to a held term joins that term's class at the next
    ///   rebuild.
    /// - fails: [`EGraphError::Table`] when the table holds no term at a place
    ///   that the walk reaches.
    /// - panics: none.
    /// - executable: none — the ensures compares the e-graph with the e-graph
    ///   before the call, which the call changes.
    ///
    /// # Errors
    /// - [`EGraphError::Table`]: a place is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term added twice, and a term over a held argument,
    ///   separate a new node from a held one.
    /// - witness: `tests::graph::a_term_is_held_with_each_argument_once`
    #[inline]
    pub fn add(
        &mut self,
        place: TermPlace,
    ) -> Result<TermPlace, EGraphError>
    {
        let mut pending = vec![(place, Visit::Enter)];
        while let Some((at, visit)) = pending.pop() {
            if self.leader(at).is_some() {
                continue;
            }
            match visit {
                Visit::Enter => {
                    let node = self.table.node(at)?;
                    pending.push((at, Visit::Leave));
                    pending.extend(
                        node.children
                            .iter()
                            .rev()
                            .map(|&child| (child, Visit::Enter)),
                    );
                },
                Visit::Leave => self.adopt(at)?,
            }
        }
        self.find(place)
    }

    /// The datum of the node at `at`, from its head and its children's data,
    /// with `roots` as the buffer of the children's roots.
    ///
    /// # Specification
    /// trivial.
    fn make(
        &mut self,
        at: TermPlace,
        roots: &mut Vec<TermPlace>,
    ) -> Result<A::Data, EGraphError>
    {
        roots.clear();
        let head = {
            let node = self.table.node(at)?;
            roots.extend(node.children.iter().copied());
            node.head
        };
        for slot in roots.iter_mut() {
            *slot = self.compress(*slot)?;
        }
        if let Some(&missing) = roots
            .iter()
            .find(|&&root| self.data.get(usize::from(root)).is_none_or(Option::is_none))
        {
            return Err(EGraphError::Unheld(missing));
        }
        Ok(self.analysis.make(head, ChildData {
            roots: roots.iter(),
            data: &self.data,
        }))
    }

    /// Hold the node at `at`, whose children the e-graph holds, in a class of
    /// its own.
    ///
    /// # Specification
    /// trivial.
    fn adopt(
        &mut self,
        at: TermPlace,
    ) -> Result<(), EGraphError>
    {
        let mut roots = mem::take(&mut self.scratch.classes);
        let datum = self.make(at, &mut roots)?;
        let index = usize::from(at);
        // The table holds `at`, so the count of its places is more than
        // `index`. Each array gets one slot for each place of the table.
        let len = self.table.issued().len();
        if self.leader.len() < len {
            self.leader.resize(len, ABSENT);
            self.members.resize(len, 0);
            self.next.resize(len, ABSENT);
            self.uses.resize_with(len, Vec::new);
            self.data.resize_with(len, || None);
            self.proof.resize(len, None);
            self.standing.resize(len, Standing::Live);
        }
        if let Some(slot) = self.leader.get_mut(index) {
            *slot = index;
        }
        if let Some(slot) = self.members.get_mut(index) {
            *slot = 1;
        }
        if let Some(slot) = self.next.get_mut(index) {
            *slot = index;
        }
        if let Some(slot) = self.data.get_mut(index) {
            *slot = Some(datum);
        }
        for &root in &roots {
            if let Some(parents) = self.uses.get_mut(usize::from(root)) {
                parents.push(at);
            }
        }
        // A congruent node already held shares this node's first child's
        // class, so the repair of that class finds it.
        if let Some(&first) = roots.first() {
            self.worklist.push(first);
        }
        self.nodes = self.nodes.saturating_add(1);
        roots.clear();
        self.scratch.classes = roots;
        Ok(())
    }

    /// Apply the instance of the equation at `equation` with `values` for its
    /// variables: hold its two sides, and join them.
    ///
    /// # Specification
    /// - ensures: the two sides under `values` lie in one class, and the
    ///   union's reason is the equation at the instance. A union of two nodes
    ///   that one class holds is kept as [`Redundant`].
    /// - fails: [`EGraphError::UnknownEquation`] when no equation stands at
    ///   `equation`; [`EGraphError::Values`] when `values` does not give one
    ///   value for each variable; [`EGraphError::Table`] when the table refuses
    ///   a substitution.
    /// - panics: none.
    /// - executable: none — the ensures compares the classes with the classes
    ///   before the call, which the call changes.
    ///
    /// # Errors
    /// - [`EGraphError::UnknownEquation`]: no equation at the place.
    /// - [`EGraphError::Values`]: the wrong number of values.
    /// - [`EGraphError::Table`]: the table refuses a substitution.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an equation whose sides lie apart, and the same
    ///   equation again, separate a merge from a redundant union.
    /// - witness: `tests::graph::a_union_inside_one_class_keeps_its_reason`
    #[inline]
    pub fn apply(
        &mut self,
        equation: EquationPlace,
        values: Vec<TermPlace>,
    ) -> Result<Joined, EGraphError>
    {
        let stated = *self
            .equations
            .get(usize::from(equation))
            .ok_or(EGraphError::UnknownEquation(equation))?;
        if values.len() != usize::from(stated.variables) {
            return Err(EGraphError::Values(equation));
        }
        let left = self.table.substituted(stated.left, &values)?;
        let right = self.table.substituted(stated.right, &values)?;
        let _left_class = self.add(left)?;
        let _right_class = self.add(right)?;
        let _new = self.applied.insert((equation, values.clone()));
        self.union(left, right, Reason::Input {
            equation,
            direction: Direction::Forward,
            values,
        })
    }

    /// Join the nodes at `left` and `right` for `reason`, read from `left` to
    /// `right`. The proof forest gains one edge, from the node of the smaller
    /// class; a union inside one class is kept as [`Redundant`].
    ///
    /// # Specification
    /// trivial.
    fn union(
        &mut self,
        left: TermPlace,
        right: TermPlace,
        reason: Reason,
    ) -> Result<Joined, EGraphError>
    {
        let (left_root, right_root) = (self.compress(left)?, self.compress(right)?);
        if left_root == right_root {
            self.redundant.push(Redundant {
                left,
                right,
                reason,
            });
            return Ok(Joined::Already);
        }
        let (left_root, right_root) = (usize::from(left_root), usize::from(right_root));
        let size = |root: usize| self.members.get(root).copied().unwrap_or(0);
        let (left_size, right_size) = (size(left_root), size(right_root));
        let (small, small_root, big, big_root, mut reason) = if left_size < right_size {
            (left, left_root, right, right_root, reason)
        }
        else {
            (right, right_root, left, left_root, reason)
        };
        if left_size >= right_size {
            reason.flip();
        }
        self.reroot(small);
        let place = self.reasons.len();
        self.reasons.push(reason);
        if let Some(slot) = self.proof.get_mut(usize::from(small)) {
            *slot = Some(Edge {
                to: usize::from(big),
                reason: place,
            });
        }
        if let Some(slot) = self.leader.get_mut(small_root) {
            *slot = big_root;
        }
        if let Some(slot) = self.members.get_mut(big_root) {
            *slot = left_size.saturating_add(right_size);
        }
        let small_next = self.next.get(small_root).copied().unwrap_or(small_root);
        let big_next = self.next.get(big_root).copied().unwrap_or(big_root);
        if let Some(slot) = self.next.get_mut(small_root) {
            *slot = big_next;
        }
        if let Some(slot) = self.next.get_mut(big_root) {
            *slot = small_next;
        }
        let mut moved = self.uses.get_mut(small_root).map_or_default(mem::take);
        if let Some(parents) = self.uses.get_mut(big_root) {
            if moved.len() > parents.len() {
                mem::swap(parents, &mut moved);
            }
            parents.append(&mut moved);
        }
        let from = self.data.get_mut(small_root).and_then(Option::take);
        if let (Some(into), Some(from)) =
            (self.data.get_mut(big_root).and_then(Option::as_mut), from)
        {
            let _growth = self.analysis.merge(into, from);
        }
        self.worklist.push(TermPlace::from(big_root));
        self.unions = self.unions.saturating_add(1);
        Ok(Joined::Merged)
    }

    /// Make `at` the root of its proof tree, each edge on the way from `at`
    /// to the old root turned round.
    ///
    /// # Specification
    /// trivial.
    fn reroot(
        &mut self,
        at: TermPlace,
    )
    {
        let mut previous: Option<Edge> = None;
        let mut here = usize::from(at);
        while let Some(slot) = self.proof.get_mut(here) {
            let Some(edge) = mem::replace(slot, previous)
            else {
                break;
            };
            if let Some(reason) = self.reasons.get_mut(edge.reason) {
                reason.flip();
            }
            previous = Some(Edge {
                to: here,
                reason: edge.reason,
            });
            here = edge.to;
        }
    }

    /// Restore congruence and the analysis invariant: repair each class of
    /// the worklist, deduplicated, until the worklist is empty.
    ///
    /// # Specification
    /// - ensures: congruent nodes lie in one class; each class holds the join
    ///   of its nodes' data; and one chunk of the worklist repairs each of its
    ///   classes once.
    /// - fails: [`EGraphError::Table`] when a held place has no term, which a
    ///   corrupt table gives.
    /// - panics: none.
    /// - executable: none — congruence is a statement about every two nodes,
    ///   which the rebuild repairs and does not compare.
    ///
    /// # Errors
    /// - [`EGraphError`]: as [`Analysis::modify`] refuses, or a held place has
    ///   no term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of unions under one class of parents repairs
    ///   that class once when the rebuild comes after the chain, and once for
    ///   each union when a rebuild follows each union.
    /// - witness: `tests::graph::the_rebuild_repairs_each_class_once`
    /// - witness: `tests::analysis::each_class_holds_the_join_of_its_nodes_data`
    #[inline]
    pub fn rebuild(&mut self) -> Result<(), EGraphError>
    {
        let mut todo = mem::take(&mut self.todo);
        while !self.worklist.is_empty() {
            todo.clear();
            todo.append(&mut self.worklist);
            for class in &mut todo {
                *class = self.compress(*class)?;
            }
            todo.sort_unstable();
            todo.dedup();
            for &class in &todo {
                self.repair(class)?;
            }
        }
        todo.clear();
        self.todo = todo;
        Ok(())
    }

    /// Repair the class of `class`: join each two parents that are congruent,
    /// keep one parent for each signature, run [`Analysis::modify`], and make
    /// each parent's datum again.
    ///
    /// # Specification
    /// trivial.
    fn repair(
        &mut self,
        class: TermPlace,
    ) -> Result<(), EGraphError>
    {
        self.repairs = self.repairs.saturating_add(1);
        let root = self.compress(class)?;
        let parents = self
            .uses
            .get_mut(usize::from(root))
            .map(mem::take)
            .ok_or(EGraphError::Unheld(class))?;
        let mut scratch = mem::take(&mut self.scratch);
        let Scratch {
            ref mut keys,
            ref mut classes,
            ref mut joins,
            ref mut kept,
        } = scratch;
        keys.clear();
        classes.clear();
        joins.clear();
        kept.clear();
        for &parent in &parents {
            if self.standing.get(usize::from(parent)) != Some(&Standing::Live) {
                continue;
            }
            let start = classes.len();
            let head = {
                let node = self.table.node(parent)?;
                classes.extend(node.children.iter().copied());
                node.head
            };
            if let Some(run) = classes.get_mut(start ..) {
                for slot in run {
                    *slot = self.compress(*slot)?;
                }
            }
            keys.push(Key {
                head,
                start,
                end: classes.len(),
                parent,
            });
        }
        let signature = |key: &Key| (key.head, classes.get(key.start .. key.end));
        keys.sort_unstable_by(|left, right| {
            signature(left)
                .cmp(&signature(right))
                .then_with(|| left.parent.cmp(&right.parent))
        });
        let mut group: Option<(Key, TermPlace)> = None;
        for key in keys.iter() {
            match group {
                Some((first, last)) if signature(&first) == signature(key) => {
                    if key.parent != last {
                        joins.push((first.parent, key.parent));
                        group = Some((first, key.parent));
                    }
                },
                Some(_) | None => {
                    kept.push(key.parent);
                    group = Some((*key, key.parent));
                },
            }
        }
        for &(stays, joins_it) in joins.iter() {
            if let Some(slot) = self.standing.get_mut(usize::from(joins_it)) {
                *slot = Standing::Retired;
            }
            let _joined = self.union(stays, joins_it, Reason::Congruence)?;
        }
        let root = self.compress(root)?;
        if let Some(list) = self.uses.get_mut(usize::from(root)) {
            list.extend(kept.iter().copied());
        }
        A::modify(self, root)?;
        for &parent in kept.iter() {
            let made = self.make(parent, classes)?;
            let parent_root = self.compress(parent)?;
            let growth = match self
                .data
                .get_mut(usize::from(parent_root))
                .and_then(Option::as_mut)
            {
                Some(datum) => self.analysis.merge(datum, made),
                None => return Err(EGraphError::Unheld(parent)),
            };
            if growth == Growth::Grew {
                self.worklist.push(parent_root);
            }
        }
        self.scratch = scratch;
        Ok(())
    }
}
