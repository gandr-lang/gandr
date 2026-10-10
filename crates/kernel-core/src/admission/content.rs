//! Schema plans instantiated in a consumer-owned, exactly interned arena.

use super::Admission;
use super::Arena;
use super::BTreeSet;
use super::Budget;
use super::Child;
use super::Guard;
use super::Natural;
use super::Node;
use super::Point;
use super::Refusal;
use super::Schema;
use super::Stage;
use super::Term;
use super::TermId;
use super::Type;
use super::TypeId;
use super::Vec;

/// A pattern coordinate has an arena identity or awaits the current row.
#[derive(Clone, Copy, Debug)]
enum Slot
{
    /// Exact identity in the bound arena, never a foreign coordinate.
    Known(TermId),
    /// No row has supplied this dependent coordinate yet.
    Pending,
}

/// Guard dependence in validated pattern-coordinate order.
#[repr(transparent)]
#[derive(Debug, Default)]
pub(super) struct Dependencies(
    /// One dependence bit for every skeleton coordinate.
    pub Vec<bool>,
);

/// Immutable dependency classification and reachable topological plan.
#[derive(Debug, Default)]
pub(super) struct Prepared
{
    /// Whether each pattern node depends on a guarded choice.
    dynamic: Dependencies,
    /// Reachable dependent nodes in child-before-parent order.
    plan: Vec<TermId>,
}

impl Prepared
{
    /// Retain the validated dependency classification and reachable plan.
    ///
    /// # Specification
    /// - ensures: the plan visits each reachable dependent node exactly once.
    /// - fails: exhausted work allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the originating work refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fanout determines changed-constructor work, not
    ///   depth.
    /// - witness: `admission::tests::affected_constructors_measure_fanout_not_depth`
    pub(super) fn build(
        dynamic: Dependencies,
        reachable: &BTreeSet<TermId>,
        budget: &mut Budget,
    ) -> Result<Self, Refusal>
    {
        let mut plan = Vec::new();
        for (index, dependent) in dynamic.0.iter().enumerate() {
            budget.spend()?;
            if *dependent && reachable.contains(&TermId(index)) {
                plan.push(TermId(index));
            }
        }
        Ok(Self { dynamic, plan })
    }

    /// Research scratch: the dependence bit per pattern coordinate.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn dynamic(&self) -> &[bool]
    {
        &self.dynamic.0
    }

    /// Research scratch: the dependent plan in child-before-parent order.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn plan(&self) -> &[TermId]
    {
        &self.plan
    }
}

/// Consumer syntax and schema coordinates, owned together so ids cannot escape
/// their namespace through arena replacement.
#[derive(Clone, Debug)]
pub(super) struct Instance
{
    /// Materialized consumer input and newly interned changed constructors.
    arena: Arena,
    /// Proposal classifiers remapped once into this arena.
    types: Vec<TypeId>,
    /// Fixed imports and reusable slots for the current row's changed nodes.
    nodes: Vec<Slot>,
}

impl Instance
{
    /// Import fixed schema content once, without walking materialized sides.
    ///
    /// # Specification
    /// - ensures: fixed terms and classifiers have exact identities in the
    ///   owned arena; each dynamic slot is initially pending.
    /// - fails: malformed schema references or exhausted work.
    /// - panics: none.
    /// - intension: imports classifiers and fixed schema nodes once per
    ///   binding; cloning the binding retains both the arena and its coordinate
    ///   map.
    ///
    /// # Errors
    /// Returns syntax, malformed-reference or work refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — same numeric classifier ids in different arenas
    ///   cannot establish content equality.
    /// - witness: `admission::tests::classifier_coordinates_are_not_content`
    /// - witness: `admission::tests::bound_arenas_preserve_exactness_and_recovery`
    pub(super) fn bind(
        schema: &Schema,
        arena: Arena,
        budget: &mut Budget,
    ) -> Result<Self, Refusal>
    {
        let mut result = Self {
            arena,
            types: Vec::with_capacity(schema.proposal.classifiers.len()),
            nodes: Vec::with_capacity(schema.proposal.nodes.len()),
        };
        for ty in &schema.proposal.classifiers {
            budget.spend()?;
            let ty = match *ty {
                | Type::Arrow(a, b) => Type::Arrow(result.classifier(a)?, result.classifier(b)?),
                | Type::Lift(inner) => Type::Lift(result.classifier(inner)?),
                | leaf => leaf,
            };
            let id = result.arena.alloc_type(ty)?;
            result.types.push(id);
        }
        for (node, dynamic) in schema.proposal.nodes.iter().zip(&schema.content.dynamic.0) {
            budget.spend()?;
            let slot = if *dynamic {
                Slot::Pending
            }
            else {
                let Node::Rigid(term) = *node
                else {
                    return Err(Refusal::Malformed);
                };
                let term = result.rebuild(term)?;
                Slot::Known(result.arena.alloc(term)?)
            };
            result.nodes.push(slot);
        }
        Ok(result)
    }

    /// Resolve one schema classifier in this arena.
    ///
    /// # Specification
    /// - ensures: returns the exact imported classifier coordinate.
    /// - fails: malformed classifier reference.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns Malformed for an absent coordinate.
    fn classifier(
        &self,
        id: TypeId,
    ) -> Result<TypeId, Refusal>
    {
        self.types.get(id.0).copied().ok_or(Refusal::Malformed)
    }

    /// Resolve a fixed or already-computed dynamic pattern coordinate.
    ///
    /// # Specification
    /// - ensures: the result belongs to this binding's arena.
    /// - fails: malformed or not-yet-computed dependency.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns Malformed on an absent or pending coordinate.
    fn resolve(
        &self,
        id: TermId,
    ) -> Result<TermId, Refusal>
    {
        match self.nodes.get(id.0).copied().ok_or(Refusal::Malformed)? {
            | Slot::Known(id) => Ok(id),
            | Slot::Pending => Err(Refusal::Malformed),
        }
    }

    /// Remap children and classifiers while preserving every rigid payload.
    ///
    /// # Specification
    /// - ensures: constructor, stage and nonclassifier payload are unchanged.
    /// - fails: malformed dependency or child shape.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns Malformed or the syntax refusal.
    fn rebuild(
        &self,
        term: Term,
    ) -> Result<Term, Refusal>
    {
        let term = match term {
            | Term::Code(ty) => Term::Code(self.classifier(ty)?),
            | Term::Lambda(ty, body) => Term::Lambda(self.classifier(ty)?, body),
            | Term::Eliminate(body, ty) => Term::Eliminate(body, self.classifier(ty)?),
            | term => term,
        };
        let mut children = [Child::Vacant; 3];
        for (child, output) in term.children().into_iter().zip(&mut children) {
            if let Child::Present(child) = child {
                *output = Child::Present(self.resolve(child)?);
            }
        }
        Ok(term.rebuild(children)?)
    }
}

/// Resolve one validated point choice to its schema-owned fixed arm.
///
/// # Specification
/// - ensures: returns the selected arm, not an arbitrary caller term.
/// - fails: missing point or unknown arm.
/// - panics: none.
///
/// # Errors
/// Returns the distinct point refusal.
fn arm(
    schema: &Schema,
    guards: &[Guard],
    point: Point,
) -> Result<TermId, Refusal>
{
    let guard = guards.get(point.0).ok_or(Refusal::MissingPoint(point))?;
    schema
        .proposal
        .arms
        .get(point.0)
        .and_then(|arms| arms.get(guard.0))
        .copied()
        .ok_or(Refusal::UnknownArm(point))
}

/// Instantiate the changed plan, then decide side equality by two arena ids.
///
/// # Specification
/// - ensures: equal ids mean exact syntax in the same interned arena, without
///   hash premises, consumer-side walks or member rule replay.
/// - fails: side mismatch, malformed reference, unknown input side or exhausted
///   work.
/// - panics: none.
/// - intension: visits only the reachable dependent plan and two live roots;
///   imported consumer term/classifier counters remain zero. Ordered-map term
///   allocation retains its logarithmic lookup cost.
///
/// # Errors
/// Returns `Refusal`, including `SidesMismatch` for differing classifier
/// content.
///
/// # Adequacy
/// - hypothesis: L2/L3 — replay, poisoned coordinates and reuse after refusal
///   distinguish exact identity from stale rows or a foreign namespace.
/// - witness: `admission::tests::schema_and_instance_refusals`
/// - witness: `admission::tests::classifier_coordinates_are_not_content`
/// - witness: `admission::tests::bound_arenas_preserve_exactness_and_recovery`
pub(super) fn compare(
    schema: &Schema,
    guards: &[Guard],
    instance: &mut Instance,
    sides: [TermId; 2],
    budget: &mut Budget,
    mut work: Admission,
) -> Result<Admission, Refusal>
{
    // Check liveness before instantiation can allocate a future numeric id.
    for side in sides {
        budget.spend()?;
        instance.arena.term(side)?;
    }
    for id in &schema.content.plan {
        budget.spend()?;
        let term = match schema.proposal.node(*id)? {
            | Node::Point(point) => {
                let arm = arm(schema, guards, point)?;
                let value = instance.resolve(arm)?;
                *instance.nodes.get_mut(id.0).ok_or(Refusal::Malformed)? = Slot::Known(value);
                continue;
            },
            | Node::Predecessor(point) => {
                let arm = arm(schema, guards, point)?;
                let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                    schema.proposal.node(arm)?
                else {
                    return Err(Refusal::Malformed);
                };
                Term::Natural(
                    Stage::Outer,
                    Natural(value.checked_sub(1).ok_or(Refusal::Transparency)?),
                )
            },
            | Node::Rigid(term) => instance.rebuild(term)?,
        };
        let value = instance.arena.alloc(term)?;
        *instance.nodes.get_mut(id.0).ok_or(Refusal::Malformed)? = Slot::Known(value);
        work.instantiations.0 = work.instantiations.0.saturating_add(1);
    }
    for (expected, actual) in [
        schema.proposal.equation.source,
        schema.proposal.equation.target,
    ]
    .into_iter()
    .zip(sides)
    {
        if instance.resolve(expected)? != actual {
            return Err(Refusal::SidesMismatch);
        }
    }
    Ok(work)
}

impl Instance
{
    /// Research scratch: a side coordinate is live in the bound arena.
    ///
    /// # Errors
    /// Returns the unknown-term refusal.
    pub(super) fn live(
        &self,
        id: TermId,
    ) -> Result<(), Refusal>
    {
        self.arena.term(id)?;
        Ok(())
    }

    /// Research scratch: resolve a fixed coordinate or a row-local one.
    ///
    /// # Errors
    /// Returns Malformed on an absent coordinate.
    fn resolve_row(
        &self,
        id: TermId,
        row: &[Option<TermId>],
    ) -> Result<TermId, Refusal>
    {
        match self.nodes.get(id.0).copied().ok_or(Refusal::Malformed)? {
            | Slot::Known(id) => Ok(id),
            | Slot::Pending => row.get(id.0).copied().flatten().ok_or(Refusal::Malformed),
        }
    }

    /// Research scratch: `rebuild` over row-local dynamic coordinates.
    ///
    /// # Errors
    /// Returns Malformed or the syntax refusal.
    fn rebuild_row(
        &self,
        term: Term,
        row: &[Option<TermId>],
    ) -> Result<Term, Refusal>
    {
        let term = match term {
            | Term::Code(ty) => Term::Code(self.classifier(ty)?),
            | Term::Lambda(ty, body) => Term::Lambda(self.classifier(ty)?, body),
            | Term::Eliminate(body, ty) => Term::Eliminate(body, self.classifier(ty)?),
            | term => term,
        };
        let mut children = [Child::Vacant; 3];
        for (child, output) in term.children().into_iter().zip(&mut children) {
            if let Child::Present(child) = child {
                *output = Child::Present(self.resolve_row(child, row)?);
            }
        }
        Ok(term.rebuild(children)?)
    }
}

/// Research scratch: evaluate the plan by lookup only; `None` when some
/// instance record is absent from the canonical arena.
///
/// # Specification
/// - ensures: `Some(roots)` exactly when every dependent record is interned; an
///   absent record means no live term equals the instance.
///
/// # Errors
/// Returns malformed-reference or work refusal.
pub(super) fn instance_roots(
    schema: &Schema,
    guards: &[Guard],
    instance: &Instance,
    row: &mut [Option<TermId>],
    budget: &mut Budget,
) -> Result<Option<[TermId; 2]>, Refusal>
{
    for id in &schema.content.plan {
        budget.spend()?;
        let term = match schema.proposal.node(*id)? {
            | Node::Point(point) => {
                let arm = arm(schema, guards, point)?;
                let value = instance.resolve_row(arm, row)?;
                *row.get_mut(id.0).ok_or(Refusal::Malformed)? = Some(value);
                continue;
            },
            | Node::Predecessor(point) => {
                let arm = arm(schema, guards, point)?;
                let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                    schema.proposal.node(arm)?
                else {
                    return Err(Refusal::Malformed);
                };
                Term::Natural(
                    Stage::Outer,
                    Natural(value.checked_sub(1).ok_or(Refusal::Transparency)?),
                )
            },
            | Node::Rigid(term) => instance.rebuild_row(term, row)?,
        };
        let Some(value) = instance.arena.find(&term)
        else {
            return Ok(None);
        };
        *row.get_mut(id.0).ok_or(Refusal::Malformed)? = Some(value);
    }
    Ok(Some([
        instance.resolve_row(schema.proposal.equation.source, row)?,
        instance.resolve_row(schema.proposal.equation.target, row)?,
    ]))
}

/// Research scratch: `compare` over a shared binding, by lookup only.
///
/// # Specification
/// - ensures: the verdict of `compare`; no allocation into the arena.
///
/// # Errors
/// Returns `Refusal`, including `SidesMismatch`.
pub(super) fn compare_shared(
    schema: &Schema,
    guards: &[Guard],
    instance: &Instance,
    sides: [TermId; 2],
    row: &mut [Option<TermId>],
    budget: &mut Budget,
    mut work: Admission,
) -> Result<Admission, Refusal>
{
    for side in sides {
        budget.spend()?;
        instance.arena.term(side)?;
    }
    let roots = instance_roots(schema, guards, instance, row, budget)?;
    work.instantiations.0 = work
        .instantiations
        .0
        .saturating_add(schema.content.plan.len());
    if roots != Some(sides) {
        return Err(Refusal::SidesMismatch);
    }
    Ok(work)
}

/// Research scratch: `compare` with producer hints; each dependent record is
/// checked against its hinted coordinate by exact equality, never searched.
///
/// # Specification
/// - ensures: success only when every hinted coordinate holds exactly the
///   rebuilt record and the roots equal the sides.
///
/// # Errors
/// Returns `Refusal`, including `SidesMismatch` for a wrong hint.
#[expect(clippy::too_many_arguments, reason = "research scratch")]
pub(super) fn compare_hinted(
    schema: &Schema,
    guards: &[Guard],
    instance: &Instance,
    sides: [TermId; 2],
    hints: &[TermId],
    row: &mut [Option<TermId>],
    budget: &mut Budget,
    work: Admission,
) -> Result<Admission, Refusal>
{
    for side in sides {
        budget.spend()?;
        instance.arena.term(side)?;
    }
    if hints.len() != schema.content.plan.len() {
        return Err(Refusal::SidesMismatch);
    }
    for (id, hint) in schema.content.plan.iter().zip(hints) {
        budget.spend()?;
        let term = match schema.proposal.node(*id)? {
            | Node::Point(point) => {
                let arm = arm(schema, guards, point)?;
                let value = instance.resolve_row(arm, row)?;
                *row.get_mut(id.0).ok_or(Refusal::Malformed)? = Some(value);
                continue;
            },
            | Node::Predecessor(point) => {
                let arm = arm(schema, guards, point)?;
                let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                    schema.proposal.node(arm)?
                else {
                    return Err(Refusal::Malformed);
                };
                Term::Natural(
                    Stage::Outer,
                    Natural(value.checked_sub(1).ok_or(Refusal::Transparency)?),
                )
            },
            | Node::Rigid(term) => instance.rebuild_row(term, row)?,
        };
        if instance.arena.term(*hint).ok() != Some(term) {
            return Err(Refusal::SidesMismatch);
        }
        *row.get_mut(id.0).ok_or(Refusal::Malformed)? = Some(*hint);
    }
    for (expected, actual) in [
        schema.proposal.equation.source,
        schema.proposal.equation.target,
    ]
    .into_iter()
    .zip(sides)
    {
        if instance.resolve_row(expected, row)? != actual {
            return Err(Refusal::SidesMismatch);
        }
    }
    Ok(work)
}
