//! Guarded local equations, validated once and compared without re-derivation.
//!
//! This module adds no rule to ordinary replay. Materialized consumer sides
//! are compared exactly; hashes confer no authority. Classifiers belong to a
//! canonical vocabulary, not to an inferred typing judgment for open equations.

mod content;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;

/// A point in a schema's dense entry order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Point(pub usize);

/// An arm in one point's dense guard order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Guard(pub usize);

/// Observed node operations, independent of elapsed time.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Work(pub usize);

/// A backward-referencing pattern node; term children index this node table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Node
{
    /// An ordinary constructor with rigid payload.
    Rigid(Term),
    /// Every occurrence selects the same guarded body.
    Point(Point),
    /// The positive outer-natural point minus one.
    Predecessor(Point),
}

/// Exact one-level pattern record; no hash decides canonical identity.
#[repr(transparent)]
#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Record([usize; 5]);

impl Node
{
    /// Encode every rigid payload and child in a disjoint constructor domain.
    ///
    /// # Specification
    /// trivial.
    fn record(self) -> Record
    {
        Record(match self {
            | Self::Rigid(Term::Variable(index)) => [0, index.0, 0, 0, 0],
            | Self::Rigid(Term::Natural(Stage::Outer, value)) => [1, value.0, 0, 0, 0],
            | Self::Rigid(Term::Natural(Stage::Inner(model), value)) => [2, model.0, value.0, 0, 0],
            | Self::Rigid(Term::Code(ty)) => [3, ty.0, 0, 0, 0],
            | Self::Rigid(Term::Lambda(ty, body)) => [4, ty.0, body.0, 0, 0],
            | Self::Rigid(Term::Apply(a, b)) => [5, a.0, b.0, 0, 0],
            | Self::Rigid(Term::Multiply(a, b)) => [6, a.0, b.0, 0, 0],
            | Self::Rigid(Term::Quote(body)) => [7, body.0, 0, 0, 0],
            | Self::Rigid(Term::Splice(body)) => [8, body.0, 0, 0, 0],
            | Self::Rigid(Term::Iterate(n, z, s)) => [9, n.0, z.0, s.0, 0],
            | Self::Rigid(Term::Eliminate(body, ty)) => [10, body.0, ty.0, 0, 0],
            | Self::Point(point) => [11, point.0, 0, 0, 0],
            | Self::Predecessor(point) => [12, point.0, 0, 0, 0],
        })
    }
}

/// A producer claim with no authority and no inheritance-cache input.
#[derive(Clone, Debug)]
pub struct Proposal
{
    /// Canonical classifier descriptors, with backward type references.
    pub classifiers: Vec<Type>,
    /// Flat syntax, including the generalized sides and distinct arm bodies.
    pub nodes: Vec<Node>,
    /// Source, target and the proposed local decision.
    pub equation: Step,
    /// Distinct guarded bodies in point order; bodies contain no points.
    pub arms: Vec<Vec<TermId>>,
}

/// A point occurrence's explicit selection, including repeated correlations.
#[derive(Clone, Copy, Debug)]
pub struct Choice
{
    /// Point whose arm is selected.
    pub point: Point,
    /// Index in that point's guard dictionary.
    pub guard: Guard,
}

/// Distinct failures at the compressed admission boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// Syntax, typing, or fuel error from the unchanged staging vocabulary.
    Syntax(StageError),
    /// Malformed schema references or a consumer bound to a different schema.
    Malformed,
    /// Validation exceeded the native proposal image's byte-sized allowance.
    SchemaWorkBound,
    /// Some guard changes a constructor, numeral class or binder observation.
    Transparency,
    /// A recorded equation does not replay under inheritance.
    CorruptStep,
    /// No selection was supplied for a point.
    MissingPoint(Point),
    /// The selected arm does not belong to this point.
    UnknownArm(Point),
    /// Repeated occurrences select different arms.
    Correlation(Point),
    /// A substitution row supplies a different classifier vocabulary.
    ClassifierMismatch,
    /// The consumer's sides are not the schema instance.
    SidesMismatch,
}

impl core::fmt::Display for Refusal
{
    /// Render the named admission refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Syntax(error) => write!(f, "syntax: {error}"),
            | Self::Malformed => f.write_str("malformed schema"),
            | Self::SchemaWorkBound => f.write_str("schema work bound"),
            | Self::Transparency => f.write_str("discrimination transparency"),
            | Self::CorruptStep => f.write_str("corrupt step"),
            | Self::MissingPoint(point) => write!(f, "missing point {}", point.0),
            | Self::UnknownArm(point) => write!(f, "unknown arm at point {}", point.0),
            | Self::Correlation(point) => write!(f, "correlation at point {}", point.0),
            | Self::ClassifierMismatch => f.write_str("classifier mismatch"),
            | Self::SidesMismatch => f.write_str("sides mismatch"),
        }
    }
}
impl core::error::Error for Refusal
{
}
impl From<StageError> for Refusal
{
    /// Preserve the underlying syntax refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: StageError) -> Self
    {
        Self::Syntax(error)
    }
}

/// Kernel-owned evidence for one local derivation schema.
#[derive(Debug)]
pub struct Schema
{
    /// Validated syntax and guard dictionaries; no caller can mutate them.
    proposal: Proposal,
    /// Dependency classification and the reachable instantiation plan.
    content: content::Prepared,
    /// Fresh skolem classifiers, including separate predecessor markers.
    skolems: Vec<TypeId>,
    /// A private arena holding only canonical classifiers.
    vocabulary: Arena,
    /// Distinct inheritance replays performed at schema time.
    checks: Work,
    /// Fuel consumed by those replays.
    replay_work: Work,
    /// Distinct dependent rigid constructors in the two side skeletons.
    affected: Work,
    /// Research scratch: fixed probe content shared by fast obligations.
    base: Option<Base>,
}

/// Research scratch: a probe arena holding every fixed skeleton node.
#[derive(Clone, Debug)]
struct Base
{
    /// Classifiers plus fixed rigid nodes.
    arena: Arena,
    /// Fixed node coordinates in the probe arena, dense by pattern index.
    known: Vec<Option<TermId>>,
}

/// Research scratch: schema-check phase boundaries for an observer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Phase
{
    /// Syntax, classification and transparency are validated.
    Prepared,
    /// One probe arena (or the shared base) is built.
    Probed,
    /// One inheritance replay finished.
    Replayed,
    /// The instantiation plan is built; the schema is complete.
    Built,
}

/// Schema-bound consumer syntax; no mutable arena replacement is exposed.
#[derive(Clone, Debug)]
pub struct Consumer<'schema>
{
    /// Exact immutable schema associated with the coordinate mapping.
    schema: &'schema Schema,
    /// Owned interned syntax and imported fixed coordinates.
    content: content::Instance,
}

/// An admissible point-ordered substitution, tied to its checked schema.
#[derive(Debug)]
pub struct Substitution<'schema>
{
    /// The only authority for this row.
    schema: &'schema Schema,
    /// Exactly one guard per point, including all repeated correlations.
    guards: Vec<Guard>,
    /// Number of supplied choices validated.
    choices: Work,
}

/// Work charged by exact instance admission.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Admission
{
    /// Guard selections, including repeated occurrences.
    pub choices: Work,
    /// Distinct dependent skeleton constructors D.
    pub affected: Work,
    /// Materialized term records imported per member; zero for bound arenas.
    pub comparisons: Work,
    /// Dynamic exact records, including predecessor payloads.
    pub instantiations: Work,
    /// Materialized classifier records imported per member; zero for bound
    /// arenas.
    pub classifiers: Work,
}

impl Proposal
{
    /// Resolve one pattern coordinate.
    ///
    /// # Specification
    /// - ensures: returns the indexed node or refuses its absent coordinate.
    /// - fails: Malformed for an out-of-range index.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::Malformed`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — malformed edges cannot become schema evidence.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    fn node(
        &self,
        id: TermId,
    ) -> Result<Node, Refusal>
    {
        self.nodes.get(id.0).copied().ok_or(Refusal::Malformed)
    }
}

impl Schema
{
    /// Establish schema inheritance and discrimination transparency once.
    ///
    /// # Specification
    /// - ensures: every distinct guarded body inherits the local equation with
    ///   other points rigid; decision observations are fixed by the guards.
    /// - fails: malformed syntax, nontransparent choices, corrupt steps or
    ///   fuel.
    /// - panics: none.
    /// - intension: one replay per distinct point/body, or one ground replay;
    ///   no imported cache supplies evidence. Scratch dies after each replay.
    ///
    /// # Errors
    /// Returns the named `Refusal` without admitting an instance.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — plain replay and altered rule/count/body cases
    ///   distinguish trusted inheritance from a producer assertion.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    /// - witness: `admission::tests::successor_and_transparency`
    #[inline]
    pub fn check_observed(
        proposal: Proposal,
        budget: &mut Budget,
        observe: &mut dyn FnMut(Phase),
        fast: bool,
    ) -> Result<Self, Refusal>
    {
        let bytes = core::mem::size_of_val(proposal.nodes.as_slice())
            .saturating_add(core::mem::size_of_val(proposal.classifiers.as_slice()))
            .saturating_add(core::mem::size_of_val(proposal.arms.as_slice()))
            .saturating_add(core::mem::size_of::<Step>());
        let bytes = proposal.arms.iter().fold(bytes, |sum, arms| {
            sum.saturating_add(core::mem::size_of_val(arms.as_slice()))
        });
        let available = budget.0.min(bytes);
        let mut limited = Budget(available);
        let result = Self::check_limited(proposal, &mut limited, observe, fast);
        budget.0 = budget.0.saturating_sub(available.saturating_sub(limited.0));
        if result
            .as_ref()
            .is_err_and(|error| *error == Refusal::Syntax(StageError::Exhausted))
            && available == bytes
        {
            return Err(Refusal::SchemaWorkBound);
        }
        result
    }

    /// Establish schema inheritance once (research scratch wrapper).
    ///
    /// # Specification
    /// - ensures: identical to `check_observed` with no observer, slow path.
    ///
    /// # Errors
    /// Returns the named `Refusal`.
    #[inline]
    pub fn check(
        proposal: Proposal,
        budget: &mut Budget,
    ) -> Result<Self, Refusal>
    {
        Self::check_observed(proposal, budget, &mut |_| {}, false)
    }

    /// Validate under the input-sized allowance selected by `check`.
    ///
    /// # Specification
    /// - ensures: only complete inheritance produces a schema.
    /// - fails: syntax, transparency, corrupt-step or work refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal` without partial authority.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared syntax cannot amplify uncharged schema work.
    /// - witness: `admission::tests::schema_work_is_bounded_by_input`
    fn check_limited(
        proposal: Proposal,
        budget: &mut Budget,
        observe: &mut dyn FnMut(Phase),
        fast: bool,
    ) -> Result<Self, Refusal>
    {
        let mut vocabulary = Arena::default();
        let mut occupied = BTreeSet::new();
        for (index, ty) in proposal.classifiers.iter().enumerate() {
            budget.spend()?;
            if vocabulary.alloc_type(*ty)? != TypeId(index) {
                return Err(Refusal::Malformed);
            }
            match *ty {
                | Type::In(model) | Type::Universe(model) | Type::Nat(Stage::Inner(model)) => {
                    occupied.insert(model);
                },
                | Type::Nat(Stage::Outer) | Type::Arrow(..) | Type::Lift(_) => {},
            }
        }
        let mut records = BTreeSet::new();
        let mut dependent = Vec::with_capacity(proposal.nodes.len());
        for (index, node) in proposal.nodes.iter().enumerate() {
            budget.spend()?;
            if !records.insert(node.record()) {
                return Err(Refusal::Malformed);
            }
            let varies = match *node {
                | Node::Point(point) | Node::Predecessor(point) => {
                    if point.0 >= proposal.arms.len() {
                        return Err(Refusal::Malformed);
                    }
                    true
                },
                | Node::Rigid(term) => {
                    if let Term::Natural(Stage::Inner(model), _) = term {
                        occupied.insert(model);
                    }
                    let mut varies = false;
                    for child in term.children().into_iter().flatten() {
                        if child.0 >= index {
                            return Err(Refusal::Malformed);
                        }
                        varies |= *dependent.get(child.0).ok_or(Refusal::Malformed)?;
                    }
                    match term {
                        | Term::Lambda(ty, _) | Term::Code(ty) | Term::Eliminate(_, ty) => {
                            vocabulary.ty(ty)?;
                        },
                        | _ => {},
                    }
                    varies
                },
            };
            dependent.push(varies);
        }
        let mut source_points = BTreeSet::new();
        let mut reached = BTreeSet::new();
        let mut pending = Vec::from([proposal.equation.source]);
        while let Some(id) = pending.pop() {
            budget.spend()?;
            if !reached.insert(id) {
                continue;
            }
            match proposal.node(id)? {
                | Node::Point(point) => {
                    source_points.insert(point);
                },
                | Node::Predecessor(_) => return Err(Refusal::Malformed),
                | Node::Rigid(term) => pending.extend(term.children().into_iter().flatten()),
            }
        }
        if source_points.len() != proposal.arms.len() {
            return Err(Refusal::Malformed);
        }
        for arms in &proposal.arms {
            if arms.is_empty() {
                return Err(Refusal::Malformed);
            }
            let mut seen = BTreeSet::new();
            for arm in arms {
                budget.spend()?;
                if *dependent.get(arm.0).ok_or(Refusal::Malformed)? || !seen.insert(*arm) {
                    return Err(Refusal::Malformed);
                }
            }
        }
        reached.clear();
        pending.extend([proposal.equation.source, proposal.equation.target]);
        let mut affected = Work(0);
        while let Some(id) = pending.pop() {
            budget.spend()?;
            if !reached.insert(id) {
                continue;
            }
            if let Node::Rigid(term) = proposal.node(id)? {
                if *dependent.get(id.0).ok_or(Refusal::Malformed)? {
                    affected.0 = affected.0.saturating_add(1);
                }
                pending.extend(term.children().into_iter().flatten());
            }
        }
        let mut skolems = Vec::with_capacity(proposal.arms.len().saturating_mul(2));
        let mut cursor = usize::MAX;
        for _ in 0 .. proposal.arms.len().saturating_mul(2) {
            budget.spend()?;
            while occupied.contains(&Model(cursor)) {
                budget.spend()?;
                cursor = cursor.checked_sub(1).ok_or(Refusal::Malformed)?;
            }
            let model = Model(cursor);
            occupied.insert(model);
            skolems.push(vocabulary.alloc_type(Type::In(model))?);
        }
        let mut schema = Self {
            proposal,
            content: content::Prepared::default(),
            skolems,
            vocabulary,
            checks: Work(0),
            replay_work: Work(0),
            affected,
            base: None,
        };
        schema.transparent(budget)?;
        observe(Phase::Prepared);
        let obligations: Vec<_> = schema
            .proposal
            .arms
            .iter()
            .enumerate()
            .flat_map(|(point, arms)| arms.iter().map(move |arm| (Point(point), *arm)))
            .collect();
        if fast {
            schema.content =
                content::Prepared::build(content::Dependencies(dependent), &reached, budget)?;
            schema.base = Some(schema.base_probe(budget)?);
            observe(Phase::Probed);
            if obligations.is_empty() {
                let fuel = schema.obligation_fast(None, budget)?;
                schema.count(fuel);
                observe(Phase::Replayed);
            }
            for (point, arm) in obligations {
                let fuel = schema.obligation_fast(Some((point, arm)), budget)?;
                schema.count(fuel);
                observe(Phase::Replayed);
            }
            observe(Phase::Built);
            return Ok(schema);
        }
        if obligations.is_empty() {
            schema.inherit(&BTreeMap::new(), budget, observe)?;
        }
        for (point, arm) in obligations {
            schema.inherit(&BTreeMap::from([(point, arm)]), budget, observe)?;
        }
        schema.content =
            content::Prepared::build(content::Dependencies(dependent), &reached, budget)?;
        observe(Phase::Built);
        Ok(schema)
    }

    /// Observe distinct inheritance replays, replay fuel, and affected nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn work(&self) -> (Work, Work, Work)
    {
        (self.checks, self.replay_work, self.affected)
    }

    /// Borrow the exact classifier namespace carried by this schema.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn classifiers(&self) -> &[Type]
    {
        &self.proposal.classifiers
    }

    /// Bind fixed schema content to an owned consumer arena once.
    ///
    /// # Specification
    /// - ensures: returned coordinates and syntax stay in one owned namespace;
    ///   cloning preserves their association with this immutable schema.
    /// - fails: malformed references or exhausted preparation work.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the originating admission refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a different arena or schema cannot reuse a positive
    ///   id comparison.
    /// - witness: `admission::tests::bound_arenas_preserve_exactness_and_recovery`
    #[inline]
    pub fn bind(
        &self,
        arena: Arena,
        budget: &mut Budget,
    ) -> Result<Consumer<'_>, Refusal>
    {
        let content = content::Instance::bind(self, arena, budget)?;
        Ok(Consumer {
            schema: self,
            content,
        })
    }

    /// Validate every supplied occurrence and require every point.
    ///
    /// # Specification
    /// - ensures: every point selects an existing arm; repeated selections
    ///   agree and the complete classifier vocabulary equals the schema's.
    /// - fails: classifier mismatch, unknown arm, correlation or missing point.
    /// - panics: none.
    /// - intension: linear in supplied choices plus classifier bytes; borrowing
    ///   the schema's own classifier slice makes that comparison constant-time.
    ///
    /// # Errors
    /// Returns the distinct substitution `Refusal`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — poisoned rows distinguish each independent premise.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    #[inline]
    pub fn substitute(
        &self,
        classifiers: &[Type],
        choices: &[Choice],
    ) -> Result<Substitution<'_>, Refusal>
    {
        if !core::ptr::eq(
            core::ptr::from_ref(classifiers),
            core::ptr::from_ref(self.classifiers()),
        ) && classifiers != self.classifiers()
        {
            return Err(Refusal::ClassifierMismatch);
        }
        let mut selected = alloc::vec![None; self.proposal.arms.len()];
        for choice in choices {
            let arms = self
                .proposal
                .arms
                .get(choice.point.0)
                .ok_or(Refusal::UnknownArm(choice.point))?;
            if choice.guard.0 >= arms.len() {
                return Err(Refusal::UnknownArm(choice.point));
            }
            let slot = selected
                .get_mut(choice.point.0)
                .ok_or(Refusal::UnknownArm(choice.point))?;
            if slot.is_some_and(|old| old != choice.guard) {
                return Err(Refusal::Correlation(choice.point));
            }
            *slot = Some(choice.guard);
        }
        let guards = selected
            .into_iter()
            .enumerate()
            .map(|(point, guard)| guard.ok_or(Refusal::MissingPoint(Point(point))))
            .collect::<Result<_, _>>()?;
        Ok(Substitution {
            schema: self,
            guards,
            choices: Work(choices.len()),
        })
    }

    /// Check all rule observations independently of inheritance replay.
    ///
    /// # Specification
    /// - ensures: guard choices cannot change the recorded rule's
    ///   discrimination; beta holes carry closed arms so binder substitution is
    ///   parametric.
    /// - fails: Transparency for a varying observation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::Transparency` or malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero/positive arms change the iteration rule.
    /// - witness: `admission::tests::successor_and_transparency`
    fn transparent(
        &self,
        budget: &mut Budget,
    ) -> Result<(), Refusal>
    {
        let source = self.proposal.node(self.proposal.equation.source)?;
        match (self.proposal.equation.rule, source) {
            | (Rule::SpliceQuote, Node::Rigid(Term::Splice(id))) => {
                if !matches!(self.proposal.node(id)?, Node::Rigid(Term::Quote(_))) {
                    return Err(Refusal::Transparency);
                }
            },
            | (Rule::QuoteSplice, Node::Rigid(Term::Quote(id))) => {
                if !matches!(self.proposal.node(id)?, Node::Rigid(Term::Splice(_))) {
                    return Err(Refusal::Transparency);
                }
            },
            | (
                Rule::IterateZero | Rule::IterateSuccessor,
                Node::Rigid(Term::Iterate(count, ..)),
            ) => {
                let counts = match self.proposal.node(count)? {
                    | Node::Point(point) => self
                        .proposal
                        .arms
                        .get(point.0)
                        .ok_or(Refusal::Malformed)?
                        .as_slice(),
                    | Node::Rigid(Term::Natural(..)) => core::slice::from_ref(&count),
                    | _ => return Err(Refusal::Transparency),
                };
                for count in counts {
                    budget.spend()?;
                    let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                        self.proposal.node(*count)?
                    else {
                        return Err(Refusal::Transparency);
                    };
                    if (value == 0) != (self.proposal.equation.rule == Rule::IterateZero) {
                        return Err(Refusal::Transparency);
                    }
                }
            },
            | (Rule::Beta, Node::Rigid(Term::Apply(head, _))) => {
                if !matches!(self.proposal.node(head)?, Node::Rigid(Term::Lambda(..))) {
                    return Err(Refusal::Transparency);
                }
                for arm in self.proposal.arms.iter().flatten() {
                    let mut pending = Vec::from([(*arm, 0_usize)]);
                    let mut seen = BTreeSet::new();
                    while let Some((id, depth)) = pending.pop() {
                        budget.spend()?;
                        if !seen.insert((id, depth)) {
                            continue;
                        }
                        let Node::Rigid(term) = self.proposal.node(id)?
                        else {
                            return Err(Refusal::Malformed);
                        };
                        if matches!(term, Term::Variable(index) if index.0 >= depth) {
                            return Err(Refusal::Transparency);
                        }
                        let depth =
                            depth.saturating_add(usize::from(matches!(term, Term::Lambda(..))));
                        pending.extend(
                            term.children()
                                .into_iter()
                                .flatten()
                                .map(|child| (child, depth)),
                        );
                    }
                }
            },
            | (Rule::Eliminate, Node::Rigid(Term::Eliminate(..)))
            | (Rule::Congruence, Node::Rigid(_)) => {},
            | _ => return Err(Refusal::Transparency),
        }
        Ok(())
    }

    /// Reify one inheritance probe, never an admitted member.
    ///
    /// # Specification
    /// - ensures: chosen arms replace points; all other points and predecessor
    ///   expressions receive fresh, distinct rigid codes.
    /// - fails: malformed syntax or staging allocation/refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal` for malformed predecessors or syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — inherited successors and corrupt targets separate
    ///   opaque probes from accepting producer claims.
    /// - witness: `admission::tests::successor_and_transparency`
    fn probe(
        &self,
        bindings: &BTreeMap<Point, TermId>,
        budget: &mut Budget,
    ) -> Result<(Arena, Step), Refusal>
    {
        budget.0 = budget
            .0
            .checked_sub(
                self.proposal
                    .classifiers
                    .len()
                    .saturating_add(self.skolems.len()),
            )
            .ok_or(StageError::Exhausted)?;
        let mut arena = self.vocabulary.clone();
        let mut known = BTreeMap::new();
        let mut pending = Vec::from([
            (self.proposal.equation.source, false),
            (self.proposal.equation.target, false),
        ]);
        while let Some((id, ready)) = pending.pop() {
            budget.spend()?;
            if known.contains_key(&id) {
                continue;
            }
            let node = self.proposal.node(id)?;
            let term = match node {
                | Node::Point(point) => {
                    if let Some(arm) = bindings.get(&point) {
                        if let Some(value) = known.get(arm) {
                            known.insert(id, *value);
                        }
                        else {
                            pending.extend([(id, true), (*arm, false)]);
                        }
                        continue;
                    }
                    Term::Code(*self.skolems.get(point.0).ok_or(Refusal::Malformed)?)
                },
                | Node::Predecessor(point) => {
                    if let Some(arm) = bindings.get(&point) {
                        let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                            self.proposal.node(*arm)?
                        else {
                            return Err(Refusal::Malformed);
                        };
                        let value = value.checked_sub(1).ok_or(Refusal::Transparency)?;
                        Term::Natural(Stage::Outer, Natural(value))
                    }
                    else {
                        Term::Code(
                            *self
                                .skolems
                                .get(point.0.saturating_add(self.proposal.arms.len()))
                                .ok_or(Refusal::Malformed)?,
                        )
                    }
                },
                | Node::Rigid(term) => {
                    if !ready {
                        pending.push((id, true));
                        pending.extend(
                            term.children()
                                .into_iter()
                                .flatten()
                                .map(|child| (child, false)),
                        );
                        continue;
                    }
                    let mut children = [Child::Vacant; 3];
                    for (source, target) in term.children().into_iter().zip(&mut children) {
                        if let Child::Present(source) = source {
                            *target =
                                Child::Present(*known.get(&source).ok_or(Refusal::Malformed)?);
                        }
                    }
                    term.rebuild(children)?
                },
            };
            known.insert(id, arena.alloc(term)?);
        }
        let source = *known
            .get(&self.proposal.equation.source)
            .ok_or(Refusal::Malformed)?;
        let target = *known
            .get(&self.proposal.equation.target)
            .ok_or(Refusal::Malformed)?;
        Ok((arena, Step {
            source,
            target,
            rule: self.proposal.equation.rule,
        }))
    }

    /// Discharge one distinct inheritance obligation using unchanged replay.
    ///
    /// # Specification
    /// - ensures: success records one valid local equation and consumed fuel.
    /// - fails: `CorruptStep` on an invalid equation; preserves exhausted fuel.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::CorruptStep` or a syntax/fuel refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a changed target or decision cannot mint a schema.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    fn inherit(
        &mut self,
        bindings: &BTreeMap<Point, TermId>,
        budget: &mut Budget,
        observe: &mut dyn FnMut(Phase),
    ) -> Result<(), Refusal>
    {
        let (mut arena, step) = self.probe(bindings, budget)?;
        observe(Phase::Probed);
        let endpoint = arena.alloc(Term::Natural(Stage::Outer, Natural(0)))?;
        let certificate = Certificate {
            source: endpoint,
            target: endpoint,
            steps: Vec::from([step]),
        };
        let before = budget.0;
        let result = crate::stage::replay(&mut arena, &[], &certificate, budget);
        self.replay_work.0 = self
            .replay_work
            .0
            .saturating_add(before.saturating_sub(budget.0));
        observe(Phase::Replayed);
        match result {
            | Ok(_) => {
                self.checks.0 = self.checks.0.saturating_add(1);
                Ok(())
            },
            | Err(StageError::Exhausted) => Err(Refusal::Syntax(StageError::Exhausted)),
            | Err(_) => Err(Refusal::CorruptStep),
        }
    }

    /// Research scratch: record one discharged obligation's fuel.
    ///
    /// # Specification
    /// trivial.
    fn count(
        &mut self,
        fuel: usize,
    )
    {
        self.checks.0 = self.checks.0.saturating_add(1);
        self.replay_work.0 = self.replay_work.0.saturating_add(fuel);
    }

    /// Research scratch: allocate every fixed rigid node once.
    ///
    /// # Specification
    /// - ensures: fixed nodes have probe coordinates; dynamic nodes stay
    ///   vacant.
    ///
    /// # Errors
    /// Returns syntax or work refusal.
    fn base_probe(
        &self,
        budget: &mut Budget,
    ) -> Result<Base, Refusal>
    {
        let dynamic = self.content.dynamic();
        let mut arena = self.vocabulary.clone();
        let mut known = alloc::vec![None; self.proposal.nodes.len()];
        for (index, node) in self.proposal.nodes.iter().enumerate() {
            budget.spend()?;
            if *dynamic.get(index).ok_or(Refusal::Malformed)? {
                continue;
            }
            let Node::Rigid(term) = *node
            else {
                return Err(Refusal::Malformed);
            };
            let mut children = [Child::Vacant; 3];
            for (source, target) in term.children().into_iter().zip(&mut children) {
                if let Child::Present(source) = source {
                    *target = Child::Present(
                        known
                            .get(source.0)
                            .copied()
                            .flatten()
                            .ok_or(Refusal::Malformed)?,
                    );
                }
            }
            let slot = known.get_mut(index).ok_or(Refusal::Malformed)?;
            *slot = Some(arena.alloc(term.rebuild(children)?)?);
        }
        Ok(Base { arena, known })
    }

    /// Research scratch: one obligation over the shared fixed base.
    ///
    /// # Specification
    /// - ensures: the same probe content as `probe`, dynamic nodes only.
    ///
    /// # Errors
    /// Returns the replay refusal, as `inherit` does.
    fn obligation_fast(
        &self,
        binding: Option<(Point, TermId)>,
        budget: &mut Budget,
    ) -> Result<usize, Refusal>
    {
        let base = self.base.as_ref().ok_or(Refusal::Malformed)?;
        budget.0 = budget
            .0
            .checked_sub(
                self.proposal
                    .classifiers
                    .len()
                    .saturating_add(self.skolems.len()),
            )
            .ok_or(StageError::Exhausted)?;
        let dynamic = self.content.dynamic();
        let mut arena = base.arena.clone();
        let mut known = base.known.clone();
        for (index, node) in self.proposal.nodes.iter().enumerate() {
            if !*dynamic.get(index).ok_or(Refusal::Malformed)? {
                continue;
            }
            budget.spend()?;
            let term = match *node {
                | Node::Point(point) => {
                    if let Some((bound, arm)) = binding
                        && bound == point
                    {
                        let value = known.get(arm.0).copied().flatten();
                        *known.get_mut(index).ok_or(Refusal::Malformed)? = value;
                        continue;
                    }
                    Term::Code(*self.skolems.get(point.0).ok_or(Refusal::Malformed)?)
                },
                | Node::Predecessor(point) => {
                    if let Some((bound, arm)) = binding
                        && bound == point
                    {
                        let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                            self.proposal.node(arm)?
                        else {
                            return Err(Refusal::Malformed);
                        };
                        Term::Natural(
                            Stage::Outer,
                            Natural(value.checked_sub(1).ok_or(Refusal::Transparency)?),
                        )
                    }
                    else {
                        Term::Code(
                            *self
                                .skolems
                                .get(point.0.saturating_add(self.proposal.arms.len()))
                                .ok_or(Refusal::Malformed)?,
                        )
                    }
                },
                | Node::Rigid(term) => {
                    let mut children = [Child::Vacant; 3];
                    for (source, target) in term.children().into_iter().zip(&mut children) {
                        if let Child::Present(source) = source {
                            *target = Child::Present(
                                known
                                    .get(source.0)
                                    .copied()
                                    .flatten()
                                    .ok_or(Refusal::Malformed)?,
                            );
                        }
                    }
                    term.rebuild(children)?
                },
            };
            *known.get_mut(index).ok_or(Refusal::Malformed)? = Some(arena.alloc(term)?);
        }
        let side = |id: TermId| known.get(id.0).copied().flatten().ok_or(Refusal::Malformed);
        let step = Step {
            source: side(self.proposal.equation.source)?,
            target: side(self.proposal.equation.target)?,
            rule: self.proposal.equation.rule,
        };
        let endpoint = arena.alloc(Term::Natural(Stage::Outer, Natural(0)))?;
        let certificate = Certificate {
            source: endpoint,
            target: endpoint,
            steps: Vec::from([step]),
        };
        let before = budget.0;
        match crate::stage::replay(&mut arena, &[], &certificate, budget) {
            | Ok(_) => Ok(before.saturating_sub(budget.0)),
            | Err(StageError::Exhausted) => Err(Refusal::Syntax(StageError::Exhausted)),
            | Err(_) => Err(Refusal::CorruptStep),
        }
    }

    /// Research scratch: the number of independent inheritance obligations.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn obligation_count(&self) -> usize
    {
        self.proposal
            .arms
            .iter()
            .map(Vec::len)
            .sum::<usize>()
            .max(1)
    }

    /// Research scratch: re-discharge obligation `index` on a fast schema.
    ///
    /// # Specification
    /// - ensures: the same replay `check_observed(.., true)` ran for `index`.
    ///
    /// # Errors
    /// Returns `Malformed` on a slow schema or an absent index.
    pub fn discharge(
        &self,
        index: usize,
        budget: &mut Budget,
    ) -> Result<usize, Refusal>
    {
        if self.proposal.arms.iter().all(Vec::is_empty) {
            return self.obligation_fast(None, budget);
        }
        let (point, arm) = self
            .proposal
            .arms
            .iter()
            .enumerate()
            .flat_map(|(point, arms)| arms.iter().map(move |arm| (Point(point), *arm)))
            .nth(index)
            .ok_or(Refusal::Malformed)?;
        self.obligation_fast(Some((point, arm)), budget)
    }

    /// Research scratch: validate a row into reusable buffers, allocation
    /// free.
    ///
    /// # Specification
    /// - ensures: the same refusals as `substitute`.
    ///
    /// # Errors
    /// Returns the substitution refusal.
    fn validate_into(
        &self,
        choices: &[Choice],
        scratch: &mut RowScratch,
    ) -> Result<(), Refusal>
    {
        scratch.selected.clear();
        scratch.selected.resize(self.proposal.arms.len(), None);
        for choice in choices {
            let arms = self
                .proposal
                .arms
                .get(choice.point.0)
                .ok_or(Refusal::UnknownArm(choice.point))?;
            if choice.guard.0 >= arms.len() {
                return Err(Refusal::UnknownArm(choice.point));
            }
            let slot = scratch
                .selected
                .get_mut(choice.point.0)
                .ok_or(Refusal::UnknownArm(choice.point))?;
            if slot.is_some_and(|old| old != choice.guard) {
                return Err(Refusal::Correlation(choice.point));
            }
            *slot = Some(choice.guard);
        }
        scratch.guards.clear();
        for (point, guard) in scratch.selected.iter().enumerate() {
            scratch
                .guards
                .push(guard.ok_or(Refusal::MissingPoint(Point(point)))?);
        }
        Ok(())
    }

    /// Research scratch: admit one row against a shared, immutable binding.
    ///
    /// # Specification
    /// - ensures: the verdict of `substitute` then `admit`, by lookup only.
    ///
    /// # Errors
    /// Returns the row or side refusal.
    pub fn admit_shared(
        &self,
        consumer: &Consumer<'_>,
        choices: &[Choice],
        equation: Step,
        scratch: &mut RowScratch,
        budget: &mut Budget,
    ) -> Result<Admission, Refusal>
    {
        if !core::ptr::eq(
            core::ptr::from_ref(self),
            core::ptr::from_ref(consumer.schema),
        ) {
            return Err(Refusal::Malformed);
        }
        if equation.rule != self.proposal.equation.rule {
            return Err(Refusal::SidesMismatch);
        }
        self.validate_into(choices, scratch)?;
        let work = Admission {
            choices: Work(choices.len()),
            affected: self.affected,
            ..Admission::default()
        };
        content::compare_shared(
            self,
            &scratch.guards,
            &consumer.content,
            [equation.source, equation.target],
            &mut scratch.row,
            budget,
            work,
        )
    }

    /// Research scratch: admit a whole family, evaluating each distinct row
    /// once.
    ///
    /// # Specification
    /// - ensures: the verdict of `admit_shared` on every row; returns the
    ///   admitted and distinct-row counts.
    ///
    /// # Errors
    /// Returns the first row or side refusal.
    pub fn admit_family_memo(
        &self,
        consumer: &Consumer<'_>,
        rows: &[Vec<Choice>],
        steps: &[Step],
        scratch: &mut RowScratch,
        budget: &mut Budget,
    ) -> Result<[usize; 2], Refusal>
    {
        if !core::ptr::eq(
            core::ptr::from_ref(self),
            core::ptr::from_ref(consumer.schema),
        ) {
            return Err(Refusal::Malformed);
        }
        let mut memo: BTreeMap<Vec<usize>, [TermId; 2]> = BTreeMap::new();
        let mut key = Vec::with_capacity(self.proposal.arms.len());
        let mut admitted = 0_usize;
        for (choices, equation) in rows.iter().zip(steps) {
            if equation.rule != self.proposal.equation.rule {
                return Err(Refusal::SidesMismatch);
            }
            self.validate_into(choices, scratch)?;
            key.clear();
            key.extend(scratch.guards.iter().map(|guard| guard.0));
            let roots = if let Some(roots) = memo.get(key.as_slice()) {
                *roots
            }
            else {
                let roots = content::instance_roots(
                    self,
                    &scratch.guards,
                    &consumer.content,
                    &mut scratch.row,
                    budget,
                )?
                .ok_or(Refusal::SidesMismatch)?;
                memo.insert(key.clone(), roots);
                roots
            };
            for side in [equation.source, equation.target] {
                consumer.content.live(side)?;
            }
            if roots != [equation.source, equation.target] {
                return Err(Refusal::SidesMismatch);
            }
            admitted = admitted.saturating_add(1);
        }
        Ok([admitted, memo.len()])
    }

    /// Research scratch: untrusted producer-side hint computation; one arena
    /// id per plan entry, or `None` when the instance is not interned.
    ///
    /// # Errors
    /// Returns the row refusal.
    pub fn hints(
        &self,
        consumer: &Consumer<'_>,
        choices: &[Choice],
        scratch: &mut RowScratch,
    ) -> Result<Option<Vec<TermId>>, Refusal>
    {
        self.validate_into(choices, scratch)?;
        let roots = content::instance_roots(
            self,
            &scratch.guards,
            &consumer.content,
            &mut scratch.row,
            &mut Budget(usize::MAX),
        )?;
        if roots.is_none() {
            return Ok(None);
        }
        Ok(Some(
            self.content
                .plan()
                .iter()
                .map(|id| {
                    scratch
                        .row
                        .get(id.0)
                        .copied()
                        .flatten()
                        .unwrap_or(TermId(usize::MAX))
                })
                .collect(),
        ))
    }

    /// Research scratch: admit a row whose dependent records arrive as
    /// producer hints; each hint is checked by one indexed read and one exact
    /// record comparison, never looked up.
    ///
    /// # Specification
    /// - ensures: success exactly when `admit_shared` succeeds and the hints
    ///   name the instance's records; wrong hints refuse, never admit.
    ///
    /// # Errors
    /// Returns the row or side refusal.
    pub fn admit_hinted(
        &self,
        consumer: &Consumer<'_>,
        choices: &[Choice],
        equation: Step,
        hints: &[TermId],
        scratch: &mut RowScratch,
        budget: &mut Budget,
    ) -> Result<Admission, Refusal>
    {
        if !core::ptr::eq(
            core::ptr::from_ref(self),
            core::ptr::from_ref(consumer.schema),
        ) {
            return Err(Refusal::Malformed);
        }
        if equation.rule != self.proposal.equation.rule {
            return Err(Refusal::SidesMismatch);
        }
        self.validate_into(choices, scratch)?;
        let work = Admission {
            choices: Work(choices.len()),
            affected: self.affected,
            ..Admission::default()
        };
        content::compare_hinted(
            self,
            &scratch.guards,
            &consumer.content,
            [equation.source, equation.target],
            hints,
            &mut scratch.row,
            budget,
            work,
        )
    }
}

/// Research scratch: reusable per-worker row buffers.
#[derive(Clone, Debug, Default)]
pub struct RowScratch
{
    /// One optional guard per point while validating.
    selected: Vec<Option<Guard>>,
    /// The validated guard per point.
    guards: Vec<Guard>,
    /// Row-local dynamic coordinates, dense by pattern index.
    row: Vec<Option<TermId>>,
}

impl RowScratch
{
    /// Buffers sized for `schema`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn new(schema: &Schema) -> Self
    {
        Self {
            selected: Vec::with_capacity(schema.proposal.arms.len()),
            guards: Vec::with_capacity(schema.proposal.arms.len()),
            row: alloc::vec![None; schema.proposal.nodes.len()],
        }
    }
}

impl Substitution<'_>
{
    /// Compare materialized consumer sides to this instance without replay.
    ///
    /// # Specification
    /// - ensures: success certifies exactly the schema's instantiated local
    ///   equation by same-arena identities, without member rule replay.
    /// - fails: `SidesMismatch` for unequal syntax or decision; `Malformed` for
    ///   a consumer bound to another schema; syntax/fuel errors.
    /// - panics: none.
    /// - intension: row validation and D plus two root liveness checks and two
    ///   exact id comparisons; no consumer-side term or classifier walk.
    ///
    /// # Errors
    /// Returns side/schema mismatch or syntax/fuel refusals.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — ordinary replay, a changed side and aliasing of
    ///   classifier coordinates distinguish exact instance admission.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    /// - witness: `admission::tests::successor_and_transparency`
    #[inline]
    pub fn admit(
        &self,
        consumer: &mut Consumer<'_>,
        equation: Step,
        budget: &mut Budget,
    ) -> Result<Admission, Refusal>
    {
        if !core::ptr::eq(
            core::ptr::from_ref(self.schema),
            core::ptr::from_ref(consumer.schema),
        ) {
            return Err(Refusal::Malformed);
        }
        if equation.rule != self.schema.proposal.equation.rule {
            return Err(Refusal::SidesMismatch);
        }
        let work = Admission {
            choices: self.choices,
            affected: self.schema.affected,
            ..Admission::default()
        };
        content::compare(
            self.schema,
            &self.guards,
            &mut consumer.content,
            [equation.source, equation.target],
            budget,
            work,
        )
    }
}

#[cfg(test)]
mod tests;
