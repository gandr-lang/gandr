//! Guarded local equations, validated once and compared without re-derivation.
//!
//! This module adds no rule to ordinary replay. Materialized consumer sides
//! are compared exactly; hashes confer no authority. Classifiers belong to a
//! canonical vocabulary, not to an inferred typing judgment for open equations.

mod content;

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
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
}

/// Schema-bound consumer syntax, immutable after binding and shared by
/// reference across rows; no mutable arena replacement is exposed.
#[derive(Clone, Debug)]
pub struct Consumer<'schema>
{
    /// Exact immutable schema associated with the coordinate mapping.
    schema: &'schema Schema,
    /// Owned interned syntax and imported fixed coordinates.
    content: content::Instance,
}

/// One point's selection while a row is validated.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Selected
{
    /// No occurrence of the point has been supplied yet.
    Open,
    /// Every supplied occurrence selected this guard.
    Chosen(Guard),
}

/// Reusable buffers for one row at a time, owned by the caller.
///
/// The buffers grow to the largest schema they serve and are rewritten by
/// every row; once sized, validating and admitting a row allocates nothing.
#[derive(Clone, Debug, Default)]
pub struct Row
{
    /// One selection per point, rewritten by every substitution.
    selected: Vec<Selected>,
    /// The current row's dependent coordinates, dense by pattern node.
    coordinates: Vec<content::Slot>,
}

/// An admissible point-ordered substitution, tied to its checked schema and
/// held in the caller's row buffers.
#[derive(Debug)]
pub struct Substitution<'schema, 'row>
{
    /// The only authority for this row.
    schema: &'schema Schema,
    /// Exactly one chosen guard per point, plus the dependent coordinates.
    row: &'row mut Row,
    /// Number of supplied choices validated.
    choices: Work,
}

/// Fixed probe content shared by every inheritance obligation of one schema.
#[derive(Clone, Debug)]
struct Base
{
    /// The vocabulary, skolems and every fixed skeleton node.
    arena: Arena,
    /// Probe coordinate per pattern node; dependent nodes stay pending.
    known: Vec<content::Slot>,
}

/// Which guarded body one inheritance obligation binds.
#[derive(Clone, Copy, Debug)]
enum Obligation
{
    /// A schema without points owes one ground replay.
    Ground,
    /// One point bound to one of its arms; every other point stays rigid.
    Arm(Point, TermId),
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
    #[spec(ensures: |ret| ret == self.nodes.get(id.0).copied().ok_or(Refusal::Malformed))]
    fn node(
        &self,
        id: TermId,
    ) -> Result<Node, Refusal>
    {
        self.nodes.get(id.0).copied().ok_or(Refusal::Malformed)
    }

    /// The schema-work allowance: the native byte size of the proposal image.
    ///
    /// # Specification
    /// trivial.
    fn allowance(&self) -> Budget
    {
        let bytes = core::mem::size_of_val(self.nodes.as_slice())
            .saturating_add(core::mem::size_of_val(self.classifiers.as_slice()))
            .saturating_add(core::mem::size_of_val(self.arms.as_slice()))
            .saturating_add(core::mem::size_of::<Step>());
        Budget(self.arms.iter().fold(bytes, |sum, arms| {
            sum.saturating_add(core::mem::size_of_val(arms.as_slice()))
        }))
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
    ///   no imported cache supplies evidence. The fixed skeleton is interned
    ///   once into a probe base; each replay clones it, interns only the
    ///   dependent nodes, and dies after replay.
    ///
    /// # Errors
    /// Returns the named `Refusal` without admitting an instance.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — plain replay and altered rule/count/body cases
    ///   distinguish trusted inheritance from a producer assertion.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    /// - witness: `admission::tests::successor_and_transparency`
    /// - witness: `admission::tests::shared_base_replays_fresh_probes`
    #[inline]
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|schema| schema.checks.0
            == schema.proposal.arms.iter().map(Vec::len).sum::<usize>().max(1)),
    )]
    pub fn check(
        proposal: Proposal,
        budget: &mut Budget,
    ) -> Result<Self, Refusal>
    {
        Self::bounded(proposal, budget)
    }

    /// Validate under an allowance bounded by the native proposal bytes.
    ///
    /// # Specification
    /// - ensures: exhausting the input-sized allowance is `SchemaWorkBound`;
    ///   exhausting the caller's smaller budget is `Exhausted`.
    /// - fails: as `check_limited`.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the named `Refusal`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared syntax cannot amplify uncharged schema work.
    /// - witness: `admission::tests::schema_work_is_bounded_by_input`
    #[spec(
        captures: [before = budget.0, allowance = proposal.allowance().0],
        ensures: |ret| budget.0 <= before
            && before.saturating_sub(budget.0) <= allowance
            && (!matches!(ret, Err(Refusal::SchemaWorkBound)) || allowance <= before)
            && (!matches!(ret, Err(Refusal::Syntax(StageError::Exhausted))) || before < allowance),
    )]
    fn bounded(
        proposal: Proposal,
        budget: &mut Budget,
    ) -> Result<Self, Refusal>
    {
        let bytes = proposal.allowance().0;
        let available = budget.0.min(bytes);
        let mut limited = Budget(available);
        let result = Self::check_limited(proposal, &mut limited);
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
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|schema|
            schema.skolems.len() == schema.proposal.arms.len().saturating_mul(2)
            && schema.checks.0 == schema.proposal.arms.iter().map(Vec::len).sum::<usize>().max(1)),
    )]
    fn check_limited(
        proposal: Proposal,
        budget: &mut Budget,
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
        };
        schema.transparent(budget)?;
        let obligations: Vec<_> = schema
            .proposal
            .arms
            .iter()
            .enumerate()
            .flat_map(|(point, arms)| {
                arms.iter()
                    .map(move |arm| Obligation::Arm(Point(point), *arm))
            })
            .collect();
        let obligations = if obligations.is_empty() {
            Vec::from([Obligation::Ground])
        }
        else {
            obligations
        };
        schema.content =
            content::Prepared::build(content::Dependencies(dependent), &reached, budget)?;
        let base = schema.base(budget)?;
        for obligation in obligations {
            schema.inherit(&base, obligation, budget)?;
        }
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
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before
            && ret.as_ref().ok().is_none_or(|consumer|
                core::ptr::eq(core::ptr::from_ref(consumer.schema), core::ptr::from_ref(self))),
    )]
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

    /// Validate every supplied occurrence into the caller's row buffers and
    /// require every point.
    ///
    /// # Specification
    /// - ensures: every point selects an existing arm; repeated selections
    ///   agree and the complete classifier vocabulary equals the schema's.
    /// - fails: classifier mismatch, unknown arm, correlation or missing point.
    /// - panics: none.
    /// - intension: linear in supplied choices plus classifier bytes; borrowing
    ///   the schema's own classifier slice makes that comparison constant-time.
    ///   The selection is written into `row`, which allocates only while it
    ///   grows to the largest schema it has served.
    ///
    /// # Errors
    /// Returns the distinct substitution `Refusal`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — poisoned rows distinguish each independent premise.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|substitution|
        core::ptr::eq(core::ptr::from_ref(substitution.schema), core::ptr::from_ref(self))
        && substitution.choices == Work(choices.len())
        && substitution.row.selected.len() == self.proposal.arms.len()
        && !substitution.row.selected.contains(&Selected::Open)))]
    pub fn substitute<'row>(
        &self,
        classifiers: &[Type],
        choices: &[Choice],
        row: &'row mut Row,
    ) -> Result<Substitution<'_, 'row>, Refusal>
    {
        self.select(classifiers, choices, &mut row.selected)?;
        Ok(Substitution {
            schema: self,
            row,
            choices: Work(choices.len()),
        })
    }

    /// Write one selection per point, refusing the first invalid premise.
    ///
    /// # Specification
    /// - ensures: on success `selected` holds exactly one chosen guard per
    ///   point, agreeing with every supplied occurrence.
    /// - fails: classifier mismatch, unknown arm, correlation or missing point.
    /// - panics: none.
    /// - intension: reuses `selected`'s capacity; allocates only to grow it.
    ///
    /// # Errors
    /// Returns the distinct substitution `Refusal`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — poisoned rows distinguish each independent premise.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    #[spec(ensures: |ret| ret.is_err() || (classifiers == self.classifiers()
        && selected.len() == self.proposal.arms.len()
        && choices.iter().all(|choice| selected.get(choice.point.0) == Some(&Selected::Chosen(choice.guard)))
        && selected.iter().zip(&self.proposal.arms).all(|(slot, arms)|
            matches!(*slot, Selected::Chosen(guard) if guard.0 < arms.len()))))]
    fn select(
        &self,
        classifiers: &[Type],
        choices: &[Choice],
        selected: &mut Vec<Selected>,
    ) -> Result<(), Refusal>
    {
        if !core::ptr::eq(
            core::ptr::from_ref(classifiers),
            core::ptr::from_ref(self.classifiers()),
        ) && classifiers != self.classifiers()
        {
            return Err(Refusal::ClassifierMismatch);
        }
        selected.clear();
        selected.resize(self.proposal.arms.len(), Selected::Open);
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
            match *slot {
                | Selected::Chosen(old) if old != choice.guard => {
                    return Err(Refusal::Correlation(choice.point));
                },
                | Selected::Open | Selected::Chosen(_) => *slot = Selected::Chosen(choice.guard),
            }
        }
        if let Some(point) = selected.iter().position(|slot| *slot == Selected::Open) {
            return Err(Refusal::MissingPoint(Point(point)));
        }
        Ok(())
    }

    /// Check all rule observations independently of inheritance replay.
    ///
    /// # Specification
    /// - ensures: guard choices cannot change the recorded rule's
    ///   discrimination: the source's head is the rigid redex former the rule
    ///   names, an iterated count's arms share its zero/positive class, and
    ///   beta holes carry closed arms so binder substitution is parametric.
    /// - fails: Transparency for a varying observation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::Transparency` or malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero/positive arms change the iteration rule.
    /// - witness: `admission::tests::successor_and_transparency`
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before && (ret.is_err() || matches!(
            (self.proposal.equation.rule, self.proposal.node(self.proposal.equation.source)),
            (Rule::SpliceQuote, Ok(Node::Rigid(Term::Splice(_))))
                | (Rule::QuoteSplice, Ok(Node::Rigid(Term::Quote(_))))
                | (Rule::IterateZero | Rule::IterateSuccessor, Ok(Node::Rigid(Term::Iterate(..))))
                | (Rule::Beta, Ok(Node::Rigid(Term::Apply(..))))
                | (Rule::Eliminate, Ok(Node::Rigid(Term::Eliminate(..))))
                | (Rule::Congruence, Ok(Node::Rigid(_)))
        )),
    )]
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

    /// Replay one reified probe equation under a closed reflexive endpoint.
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
    #[spec(
        captures: [before = budget.0, checks = self.checks.0, replayed = self.replay_work.0],
        ensures: |ret| budget.0 <= before
            && self.replay_work.0 == replayed.saturating_add(before.saturating_sub(budget.0))
            && self.checks.0 == checks.saturating_add(usize::from(ret.is_ok())),
    )]
    fn discharge(
        &mut self,
        mut arena: Arena,
        step: Step,
        budget: &mut Budget,
    ) -> Result<(), Refusal>
    {
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
        match result {
            | Ok(_) => {
                self.checks.0 = self.checks.0.saturating_add(1);
                Ok(())
            },
            | Err(StageError::Exhausted) => Err(Refusal::Syntax(StageError::Exhausted)),
            | Err(_) => Err(Refusal::CorruptStep),
        }
    }

    /// Intern the vocabulary, skolems and every fixed skeleton node once.
    ///
    /// # Specification
    /// - ensures: every fixed node has a probe coordinate holding its exact
    ///   syntax; every dependent node is pending.
    /// - fails: malformed syntax or exhausted work.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal` for malformed syntax or exhausted work.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every obligation over the base replays the probe
    ///   equation a fresh probe of the same binding reifies.
    /// - witness: `admission::tests::shared_base_replays_fresh_probes`
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|base|
            base.known.len() == self.proposal.nodes.len()
            && base.known.iter().zip(&self.proposal.nodes).enumerate().all(|(index, (slot, node))|
                match (self.content.dependence(TermId(index)), *slot, *node) {
                    (Ok(content::Dependence::Dependent), content::Slot::Pending, _) => true,
                    (Ok(content::Dependence::Fixed), content::Slot::Known(id), Node::Rigid(term)) =>
                        content::relink(term, &base.known).is_ok_and(|term| base.arena.term(id) == Ok(term)),
                    _ => false,
                })),
    )]
    fn base(
        &self,
        budget: &mut Budget,
    ) -> Result<Base, Refusal>
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
        let mut known = Vec::with_capacity(self.proposal.nodes.len());
        for (index, node) in self.proposal.nodes.iter().enumerate() {
            budget.spend()?;
            let dependence = self.content.dependence(TermId(index))?;
            let slot = match (dependence, *node) {
                | (content::Dependence::Dependent, _) => content::Slot::Pending,
                | (content::Dependence::Fixed, Node::Rigid(term)) => {
                    let term = content::relink(term, &known)?;
                    content::Slot::Known(arena.alloc(term)?)
                },
                | (content::Dependence::Fixed, Node::Point(_) | Node::Predecessor(_)) => {
                    return Err(Refusal::Malformed);
                },
            };
            known.push(slot);
        }
        Ok(Base { arena, known })
    }

    /// Discharge one inheritance obligation over the shared probe base.
    ///
    /// # Specification
    /// - ensures: replays the probe equation of the obligation's binding: the
    ///   bound point takes its arm, every other point and predecessor a fresh
    ///   rigid code.
    /// - fails: `CorruptStep` on an invalid equation; malformed syntax or
    ///   exhausted work.
    /// - panics: none.
    /// - intension: charges the vocabulary and one unit per pattern node, the
    ///   size of the base clone; interns only dependent nodes.
    ///
    /// # Errors
    /// Returns `Refusal::CorruptStep` or a syntax/fuel refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — fresh probes and corrupt steps distinguish a
    ///   shared base from a weakened probe.
    /// - witness: `admission::tests::shared_base_replays_fresh_probes`
    /// - witness: `admission::tests::schema_and_instance_refusals`
    #[spec(
        captures: [before = budget.0, checks = self.checks.0],
        ensures: |ret| budget.0 <= before && (ret.is_err() || self.checks.0 == checks.saturating_add(1)),
    )]
    fn inherit(
        &mut self,
        base: &Base,
        obligation: Obligation,
        budget: &mut Budget,
    ) -> Result<(), Refusal>
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
        let mut arena = base.arena.clone();
        let mut known = base.known.clone();
        for (index, node) in self.proposal.nodes.iter().enumerate() {
            budget.spend()?;
            let dependence = self.content.dependence(TermId(index))?;
            if dependence == content::Dependence::Fixed {
                continue;
            }
            let term = match (*node, obligation) {
                | (Node::Point(point), Obligation::Arm(bound, arm)) if point == bound => {
                    let value = known.get(arm.0).ok_or(Refusal::Malformed)?.id()?;
                    *known.get_mut(index).ok_or(Refusal::Malformed)? = content::Slot::Known(value);
                    continue;
                },
                | (Node::Point(point), _) => {
                    Term::Code(*self.skolems.get(point.0).ok_or(Refusal::Malformed)?)
                },
                | (Node::Predecessor(point), Obligation::Arm(bound, arm)) if point == bound => {
                    let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                        self.proposal.node(arm)?
                    else {
                        return Err(Refusal::Malformed);
                    };
                    Term::Natural(
                        Stage::Outer,
                        Natural(value.checked_sub(1).ok_or(Refusal::Transparency)?),
                    )
                },
                | (Node::Predecessor(point), _) => Term::Code(
                    *self
                        .skolems
                        .get(point.0.saturating_add(self.proposal.arms.len()))
                        .ok_or(Refusal::Malformed)?,
                ),
                | (Node::Rigid(term), _) => content::relink(term, &known)?,
            };
            *known.get_mut(index).ok_or(Refusal::Malformed)? =
                content::Slot::Known(arena.alloc(term)?);
        }
        let side = |id: TermId| known.get(id.0).ok_or(Refusal::Malformed)?.id();
        let step = Step {
            source: side(self.proposal.equation.source)?,
            target: side(self.proposal.equation.target)?,
            rule: self.proposal.equation.rule,
        };
        self.discharge(arena, step, budget)
    }
}

impl Substitution<'_, '_>
{
    /// Compare materialized consumer sides to this instance without replay,
    /// by lookup in the shared binding.
    ///
    /// # Specification
    /// - ensures: success certifies exactly the schema's instantiated local
    ///   equation by same-arena identities, without member rule replay; the
    ///   binding is read, never extended.
    /// - fails: `SidesMismatch` for unequal syntax or decision, including an
    ///   instance record absent from the binding; `Malformed` for a consumer
    ///   bound to another schema; syntax/fuel errors.
    /// - panics: none.
    /// - intension: row validation and D exact lookups plus two root liveness
    ///   checks and two exact id comparisons; no consumer-side term or
    ///   classifier walk and no allocation once the row buffers are sized. The
    ///   binding's arena holds every record of each live term, so a record it
    ///   lacks belongs to no live side.
    ///
    /// # Errors
    /// Returns side/schema mismatch or syntax/fuel refusals.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — ordinary replay, a changed side and aliasing of
    ///   classifier coordinates distinguish exact instance admission.
    /// - witness: `admission::tests::schema_and_instance_refusals`
    /// - witness: `admission::tests::successor_and_transparency`
    /// - witness: `admission::tests::rows_absent_from_the_binding_refuse`
    #[inline]
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|work|
            core::ptr::eq(core::ptr::from_ref(self.schema), core::ptr::from_ref(consumer.schema))
            && equation.rule == self.schema.proposal.equation.rule
            && work.choices == self.choices
            && work.affected == self.schema.affected
            && work.comparisons == Work(0)
            && work.classifiers == Work(0)),
    )]
    pub fn admit(
        &mut self,
        consumer: &Consumer<'_>,
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
        let Row {
            ref selected,
            ref mut coordinates,
        } = *self.row;
        content::compare(
            self.schema,
            selected,
            &consumer.content,
            [equation.source, equation.target],
            coordinates,
            budget,
            work,
        )
    }
}

#[cfg(test)]
mod tests;
