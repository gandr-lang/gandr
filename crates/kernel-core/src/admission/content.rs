//! Schema plans instantiated against a consumer-owned, exactly interned arena.

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::Admission;
use super::Arena;
use super::BTreeSet;
use super::Budget;
use super::Child;
use super::Natural;
use super::Node;
use super::Point;
use super::Refusal;
use super::Schema;
use super::Selected;
use super::Stage;
use super::Term;
use super::TermId;
use super::Type;
use super::TypeId;
use super::Vec;

/// A pattern coordinate has an arena identity or awaits the current row.
#[derive(Clone, Copy, Debug)]
pub(super) enum Slot
{
    /// Exact identity in the bound arena, never a foreign coordinate.
    Known(TermId),
    /// No row has supplied this dependent coordinate yet.
    Pending,
}

impl Slot
{
    /// The arena identity a slot holds.
    ///
    /// # Specification
    /// - ensures: returns the known coordinate.
    /// - fails: `Malformed` for a pending slot.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::Malformed` for a pending slot.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every base, probe and row resolution reads a slot
    ///   through this projection under enforcement; a pending read would refuse
    ///   the schemas these witnesses check.
    /// - witness: `admission::tests::shared_base_replays_fresh_probes`
    /// - witness: `admission::tests::schema_and_instance_refusals`
    #[spec(ensures: |ret| match self {
        Self::Known(id) => matches!(ret, Ok(found) if found.0 == id.0),
        Self::Pending => matches!(ret, Err(Refusal::Malformed)),
    })]
    pub(super) const fn id(self) -> Result<TermId, Refusal>
    {
        match self {
            | Self::Known(id) => Ok(id),
            | Self::Pending => Err(Refusal::Malformed),
        }
    }
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
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|prepared|
            prepared.plan.is_sorted_by(|left, right| left < right)
            && prepared.plan.iter().all(|id| reachable.contains(id) && prepared.dynamic.0.get(id.0) == Some(&true))
            && prepared.plan.len() == prepared.dynamic.0.iter().enumerate()
                .filter(|&(index, dependent)| *dependent && reachable.contains(&TermId(index))).count()),
    )]
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

    /// Whether a pattern coordinate depends on a guarded choice.
    ///
    /// # Specification
    /// - ensures: returns the validated dependence of the coordinate.
    /// - fails: `Malformed` for an absent coordinate.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::Malformed` for an absent coordinate.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the probe base and every obligation classify each
    ///   pattern node through this projection; swapping the classes changes
    ///   which nodes the shared base holds.
    /// - witness: `admission::tests::shared_base_replays_fresh_probes`
    /// - witness: `admission::tests::affected_constructors_measure_fanout_not_depth`
    #[spec(ensures: |ret| match ret {
        Ok(Dependence::Dependent) => self.dynamic.0.get(id.0) == Some(&true),
        Ok(Dependence::Fixed) => self.dynamic.0.get(id.0) == Some(&false),
        Err(error) => error == Refusal::Malformed && self.dynamic.0.len() <= id.0,
    })]
    pub(super) fn dependence(
        &self,
        id: TermId,
    ) -> Result<Dependence, Refusal>
    {
        match self.dynamic.0.get(id.0).copied() {
            | Some(true) => Ok(Dependence::Dependent),
            | Some(false) => Ok(Dependence::Fixed),
            | None => Err(Refusal::Malformed),
        }
    }
}

/// Whether a pattern coordinate is fixed or chosen per row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Dependence
{
    /// Every row shares this coordinate's content.
    Fixed,
    /// Some guard choice changes this coordinate's content.
    Dependent,
}

/// Consumer syntax and schema coordinates, owned together so ids cannot escape
/// their namespace through arena replacement.
#[derive(Clone, Debug)]
pub(super) struct Instance
{
    /// Materialized consumer input, never extended by a lookup row.
    arena: Arena,
    /// Proposal classifiers remapped once into this arena.
    types: Vec<TypeId>,
    /// Fixed imports; dependent coordinates stay pending and live in rows.
    nodes: Vec<Slot>,
}

impl Instance
{
    /// Import fixed schema content once, without walking materialized sides.
    ///
    /// # Specification
    /// - ensures: fixed terms and classifiers have exact identities in the
    ///   owned arena; each dynamic slot is pending.
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
    #[spec(
        captures: before = budget.0,
        ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|instance|
            instance.types.len() == schema.proposal.classifiers.len()
            && instance.types.iter().all(|ty| instance.arena.ty(*ty).is_ok())
            && instance.nodes.len() == schema.proposal.nodes.len()
            && instance.nodes.iter().zip(&schema.content.dynamic.0).all(|(slot, dynamic)| match *slot {
                Slot::Pending => *dynamic,
                Slot::Known(id) => !*dynamic && instance.arena.term(id).is_ok(),
            })),
    )]
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
                let term = result.rebuild(term, &[])?;
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal numeric classifier ids in another arena must
    ///   not stand for the imported classifier.
    /// - witness: `admission::tests::classifier_coordinates_are_not_content`
    #[spec(ensures: |ret| match ret {
        Ok(found) => self.types.get(id.0) == Some(&found) && self.arena.ty(found).is_ok(),
        Err(error) => error == Refusal::Malformed && self.types.len() <= id.0,
    })]
    fn classifier(
        &self,
        id: TypeId,
    ) -> Result<TypeId, Refusal>
    {
        self.types.get(id.0).copied().ok_or(Refusal::Malformed)
    }

    /// Resolve a fixed coordinate from the binding or a dependent coordinate
    /// from the current row.
    ///
    /// # Specification
    /// - ensures: the result belongs to this binding's arena.
    /// - fails: malformed or not-yet-computed dependency.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns Malformed on an absent or pending coordinate.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — rows reuse one binding while dependent slots
    ///   change; a stale or foreign coordinate would change a verdict.
    /// - witness: `admission::tests::bound_arenas_preserve_exactness_and_recovery`
    /// - witness: `admission::tests::rows_absent_from_the_binding_refuse`
    #[spec(ensures: |ret| match ret {
        Ok(found) => self.arena.term(found).is_ok() && match self.nodes.get(id.0) {
            Some(&Slot::Known(known)) => known == found,
            Some(&Slot::Pending) => matches!(coordinates.get(id.0), Some(&Slot::Known(row)) if row == found),
            None => false,
        },
        Err(error) => error == Refusal::Malformed,
    })]
    fn locate(
        &self,
        id: TermId,
        coordinates: &[Slot],
    ) -> Result<TermId, Refusal>
    {
        match self.nodes.get(id.0).copied().ok_or(Refusal::Malformed)? {
            | Slot::Known(id) => Ok(id),
            | Slot::Pending => coordinates.get(id.0).ok_or(Refusal::Malformed)?.id(),
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — classifier coordinates remapped into the binding,
    ///   unlike equal numeric ids, decide exact content.
    /// - witness: `admission::tests::classifier_coordinates_are_not_content`
    /// - witness: `admission::tests::schema_and_instance_refusals`
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|rebuilt|
        core::mem::discriminant(rebuilt) == core::mem::discriminant(&term)
        && (!matches!(term, Term::Natural(..) | Term::Variable(_)) || *rebuilt == term)
        && rebuilt.children().into_iter().zip(term.children()).all(|pair| match pair {
            (Child::Present(new), Child::Present(old)) => self.locate(old, coordinates) == Ok(new),
            (Child::Vacant, Child::Vacant) => true,
            _ => false,
        })))]
    fn rebuild(
        &self,
        term: Term,
        coordinates: &[Slot],
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
                *output = Child::Present(self.locate(child, coordinates)?);
            }
        }
        Ok(term.rebuild(children)?)
    }
}

/// Rebuild a pattern term over probe coordinates, keeping its classifiers.
///
/// # Specification
/// - ensures: constructor, stage and payload are unchanged; each child is
///   replaced by its known probe coordinate.
/// - fails: `Malformed` for a pending or absent child.
/// - panics: none.
///
/// # Errors
/// Returns Malformed or the syntax refusal.
///
/// # Adequacy
/// - hypothesis: L2 — a relinked probe that dropped a classifier or a child
///   would replay a different equation than a fresh probe reifies.
/// - witness: `admission::tests::shared_base_replays_fresh_probes`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|rebuilt|
    core::mem::discriminant(rebuilt) == core::mem::discriminant(&term)
    && match (term, *rebuilt) {
        (Term::Code(old), Term::Code(new))
        | (Term::Lambda(old, _), Term::Lambda(new, _))
        | (Term::Eliminate(_, old), Term::Eliminate(_, new)) => old == new,
        (Term::Natural(..) | Term::Variable(_), _) => *rebuilt == term,
        _ => true,
    }
    && rebuilt.children().into_iter().zip(term.children()).all(|pair| match pair {
        (Child::Present(new), Child::Present(old)) => matches!(known.get(old.0), Some(Slot::Known(id)) if *id == new),
        (Child::Vacant, Child::Vacant) => true,
        _ => false,
    })))]
pub(super) fn relink(
    term: Term,
    known: &[Slot],
) -> Result<Term, Refusal>
{
    let mut children = [Child::Vacant; 3];
    for (child, output) in term.children().into_iter().zip(&mut children) {
        if let Child::Present(child) = child {
            *output = Child::Present(known.get(child.0).ok_or(Refusal::Malformed)?.id()?);
        }
    }
    Ok(term.rebuild(children)?)
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
///
/// # Adequacy
/// - hypothesis: L3 — unknown arms and missing points are distinct refusals of
///   poisoned rows.
/// - witness: `admission::tests::schema_and_instance_refusals`
#[spec(ensures: |ret| match ret {
    Ok(found) => matches!(selected.get(point.0), Some(Selected::Chosen(guard))
        if schema.proposal.arms.get(point.0).and_then(|arms| arms.get(guard.0)) == Some(&found)),
    Err(error) => error == Refusal::MissingPoint(point) || error == Refusal::UnknownArm(point),
})]
fn arm(
    schema: &Schema,
    selected: &[Selected],
    point: Point,
) -> Result<TermId, Refusal>
{
    let Selected::Chosen(guard) = *selected.get(point.0).ok_or(Refusal::MissingPoint(point))?
    else {
        return Err(Refusal::MissingPoint(point));
    };
    schema
        .proposal
        .arms
        .get(point.0)
        .and_then(|arms| arms.get(guard.0))
        .copied()
        .ok_or(Refusal::UnknownArm(point))
}

/// What one dependent plan entry denotes for the current row.
enum Planned
{
    /// A point occurrence: the binding's coordinate of its chosen arm.
    Bound(TermId),
    /// A dependent record whose identity the binding decides.
    Record(Term),
}

/// Denote one dependent plan entry under the row's selection.
///
/// # Specification
/// - ensures: a point denotes its chosen fixed arm; a predecessor its arm's
///   outer numeral minus one; a rigid node its children's row coordinates.
/// - fails: malformed reference, missing point, unknown arm or a zero
///   predecessor.
/// - panics: none.
///
/// # Errors
/// Returns the originating `Refusal`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — successor rows denote predecessor records and
///   cancellation rows denote rebuilt records; a wrong denotation changes the
///   admitted sides.
/// - witness: `admission::tests::successor_and_transparency`
/// - witness: `admission::tests::schema_and_instance_refusals`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|planned| match (schema.proposal.node(id), planned) {
    (Ok(Node::Point(point)), &Planned::Bound(value)) => arm(schema, selected, point)
        .is_ok_and(|arm| instance.locate(arm, coordinates) == Ok(value)),
    (Ok(Node::Predecessor(point)), &Planned::Record(Term::Natural(Stage::Outer, Natural(value)))) =>
        arm(schema, selected, point).is_ok_and(|arm| schema.proposal.node(arm)
            == Ok(Node::Rigid(Term::Natural(Stage::Outer, Natural(value.saturating_add(1)))))),
    (Ok(Node::Rigid(term)), &Planned::Record(record)) => instance.rebuild(term, coordinates) == Ok(record),
    _ => false,
}))]
fn planned(
    schema: &Schema,
    selected: &[Selected],
    instance: &Instance,
    coordinates: &[Slot],
    id: TermId,
) -> Result<Planned, Refusal>
{
    Ok(match schema.proposal.node(id)? {
        | Node::Point(point) => {
            let arm = arm(schema, selected, point)?;
            Planned::Bound(instance.locate(arm, coordinates)?)
        },
        | Node::Predecessor(point) => {
            let arm = arm(schema, selected, point)?;
            let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                schema.proposal.node(arm)?
            else {
                return Err(Refusal::Malformed);
            };
            Planned::Record(Term::Natural(
                Stage::Outer,
                Natural(value.checked_sub(1).ok_or(Refusal::Transparency)?),
            ))
        },
        | Node::Rigid(term) => Planned::Record(instance.rebuild(term, coordinates)?),
    })
}

/// Size the row's coordinate buffer for a schema without shrinking it.
///
/// # Specification
/// - ensures: every pattern node has a coordinate slot.
/// - panics: none.
/// - intension: allocates only while the buffer grows.
///
/// # Adequacy
/// - hypothesis: L2 — rows of a larger schema after a smaller one reuse one
///   buffer; an undersized buffer refuses their coordinates as malformed.
/// - witness: `admission::tests::rows_absent_from_the_binding_refuse`
#[spec(
    captures: before = coordinates.len(),
    ensures: |()| coordinates.len() == before.max(schema.proposal.nodes.len()),
)]
fn reserve(
    schema: &Schema,
    coordinates: &mut Vec<Slot>,
)
{
    if coordinates.len() < schema.proposal.nodes.len() {
        coordinates.resize(schema.proposal.nodes.len(), Slot::Pending);
    }
}

/// Decide side equality by two arena ids once the plan is resolved.
///
/// # Specification
/// - ensures: success exactly when both resolved roots equal the sides.
/// - fails: `SidesMismatch` for a differing root; `Malformed` for a pending
///   root.
/// - panics: none.
///
/// # Errors
/// Returns `Refusal`.
///
/// # Adequacy
/// - hypothesis: L3 — a changed side refuses as `SidesMismatch` while the
///   unchanged member admits.
/// - witness: `admission::tests::schema_and_instance_refusals`
#[spec(ensures: |ret| ret.is_err() || [schema.proposal.equation.source, schema.proposal.equation.target]
    .into_iter().zip(sides).all(|(expected, actual)| instance.locate(expected, coordinates) == Ok(actual)))]
fn roots(
    schema: &Schema,
    instance: &Instance,
    coordinates: &[Slot],
    sides: [TermId; 2],
) -> Result<(), Refusal>
{
    for (expected, actual) in [
        schema.proposal.equation.source,
        schema.proposal.equation.target,
    ]
    .into_iter()
    .zip(sides)
    {
        if instance.locate(expected, coordinates)? != actual {
            return Err(Refusal::SidesMismatch);
        }
    }
    Ok(())
}

/// Look up the changed plan in the shared binding, then decide side equality
/// by two arena ids.
///
/// # Specification
/// - ensures: equal ids mean exact syntax in the same interned arena, without
///   hash premises, consumer-side walks, member rule replay or any write to the
///   binding.
/// - fails: side mismatch, including a record the binding lacks; malformed
///   reference, unknown input side or exhausted work.
/// - panics: none.
/// - intension: visits only the reachable dependent plan and two live roots;
///   imported consumer term/classifier counters remain zero. Ordered-map lookup
///   retains its logarithmic cost. A live side's every record is interned, so
///   an absent record is an unequal side, never an unknown one.
///
/// # Errors
/// Returns `Refusal`, including `SidesMismatch` for differing classifier
/// content.
///
/// # Adequacy
/// - hypothesis: L2/L3 — replay, poisoned coordinates, absent records and reuse
///   after refusal distinguish exact identity from stale rows or a foreign
///   namespace.
/// - witness: `admission::tests::schema_and_instance_refusals`
/// - witness: `admission::tests::classifier_coordinates_are_not_content`
/// - witness: `admission::tests::bound_arenas_preserve_exactness_and_recovery`
/// - witness: `admission::tests::rows_absent_from_the_binding_refuse`
#[spec(
    captures: [before = budget.0, instantiated = work.instantiations.0],
    ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|done|
        done.instantiations.0 >= instantiated
        && done.instantiations.0 <= instantiated.saturating_add(schema.content.plan.len())
        && roots(schema, instance, coordinates.as_slice(), sides).is_ok()),
)]
pub(super) fn compare(
    schema: &Schema,
    selected: &[Selected],
    instance: &Instance,
    sides: [TermId; 2],
    coordinates: &mut Vec<Slot>,
    budget: &mut Budget,
    mut work: Admission,
) -> Result<Admission, Refusal>
{
    for side in sides {
        budget.spend()?;
        instance.arena.term(side)?;
    }
    reserve(schema, coordinates);
    for id in &schema.content.plan {
        budget.spend()?;
        let value = match planned(schema, selected, instance, coordinates, *id)? {
            | Planned::Bound(value) => value,
            | Planned::Record(term) => {
                work.instantiations.0 = work.instantiations.0.saturating_add(1);
                match instance.arena.find(&term) {
                    | Maybe::Present(value) => value,
                    | Maybe::Absent(_) => return Err(Refusal::SidesMismatch),
                }
            },
        };
        *coordinates.get_mut(id.0).ok_or(Refusal::Malformed)? = Slot::Known(value);
    }
    roots(schema, instance, coordinates, sides)?;
    Ok(work)
}
