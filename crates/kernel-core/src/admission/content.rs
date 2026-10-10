//! Schema plans instantiated against a consumer-owned, exactly interned arena.

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
/// - witness: `admission::tests::lookup_rows_agree_with_minting_rows`
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

/// Spike control: intern the changed plan into an owned consumer clone, as
/// the original row did, then decide side equality by two arena ids.
///
/// # Specification
/// - ensures: the verdict and counters of `compare` on a live consumer.
/// - fails: as `compare`.
/// - panics: none.
///
/// # Errors
/// Returns `Refusal`.
///
/// # Adequacy
/// - hypothesis: L2 — the observer compares both row shapes per member.
/// - witness: `admission::tests::lookup_rows_agree_with_minting_rows`
pub(super) fn compare_minting(
    schema: &Schema,
    selected: &[Selected],
    instance: &mut Instance,
    sides: [TermId; 2],
    coordinates: &mut Vec<Slot>,
    budget: &mut Budget,
    mut work: Admission,
) -> Result<Admission, Refusal>
{
    // Check liveness before instantiation can allocate a future numeric id.
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
                instance.arena.alloc(term)?
            },
        };
        *coordinates.get_mut(id.0).ok_or(Refusal::Malformed)? = Slot::Known(value);
    }
    roots(schema, instance, coordinates, sides)?;
    Ok(work)
}
