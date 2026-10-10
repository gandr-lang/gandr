//! Exact content records: immutable schema dictionary plus per-member overlay.

use super::Admission;
use super::Arena;
use super::BTreeMap;
use super::BTreeSet;
use super::Budget;
use super::Child;
use super::Guard;
use super::Natural;
use super::Node;
use super::Point;
use super::Proposal;
use super::Record;
use super::Refusal;
use super::Schema;
use super::Stage;
use super::Term;
use super::TermId;
use super::Type;
use super::TypeId;
use super::Vec;
use super::Work;

/// An exact content coordinate inside one schema and one member overlay.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ContentId(usize);

/// A pattern coordinate either has fixed content or needs a row selection.
#[derive(Clone, Copy, Debug)]
enum Slot
{
    /// Content already interned by the kernel.
    Fixed(ContentId),
    /// Point-dependent content computed only in the member overlay.
    Dynamic,
}

/// Schema-owned exact records and the topological changed-constructor plan.
#[derive(Debug, Default)]
pub(super) struct Prepared
{
    /// Injective one-level records; no digest equality is consulted.
    records: BTreeMap<Record, ContentId>,
    /// Fixed content per pattern coordinate, including every guarded body.
    nodes: Vec<Slot>,
    /// Classifier content in the proposal's canonical type order.
    types: Vec<ContentId>,
    /// Reachable dependent nodes in dependency order.
    plan: Vec<TermId>,
}

/// Member-local records, borrowing the validated immutable schema dictionary.
struct Overlay<'schema>
{
    /// Read-only fixed content, shared safely between scoped workers.
    fixed: &'schema Prepared,
    /// Only content absent from the schema dictionary is allocated here.
    records: BTreeMap<Record, ContentId>,
}

impl Overlay<'_>
{
    /// Intern an exact one-level record in this member's namespace.
    ///
    /// # Specification
    /// trivial.
    fn intern(
        &mut self,
        record: Record,
    ) -> ContentId
    {
        if let Some(id) = self
            .fixed
            .records
            .get(&record)
            .or_else(|| self.records.get(&record))
        {
            return *id;
        }
        let id = ContentId(self.fixed.records.len().saturating_add(self.records.len()));
        self.records.insert(record, id);
        id
    }
}

/// Encode a classifier after its children have exact content coordinates.
///
/// # Specification
/// trivial.
fn classifier(ty: Type) -> Record
{
    Record(match ty {
        | Type::In(model) => [13, model.0, 0, 0, 0],
        | Type::Universe(model) => [14, model.0, 0, 0, 0],
        | Type::Nat(Stage::Outer) => [15, 0, 0, 0, 0],
        | Type::Nat(Stage::Inner(model)) => [16, model.0, 0, 0, 0],
        | Type::Arrow(a, b) => [17, a.0, b.0, 0, 0],
        | Type::Lift(inner) => [18, inner.0, 0, 0, 0],
    })
}

impl Prepared
{
    /// Prepare immutable content once, keeping only dynamic work in the plan.
    ///
    /// # Specification
    /// - ensures: fixed arms and constructors have exact content identities;
    ///   the plan contains only dependent nodes reachable from the sides.
    /// - fails: malformed dependencies or the input-sized work allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal` from malformed content or fuel.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — aliasing and repeated points cannot change
    ///   equality.
    /// - witness: `admission::tests::classifier_coordinates_are_not_content`
    /// - witness: `admission::tests::successor_and_transparency`
    pub(super) fn build(
        proposal: &Proposal,
        budget: &mut Budget,
    ) -> Result<Self, Refusal>
    {
        let mut result = Self::default();
        for ty in &proposal.classifiers {
            budget.spend()?;
            let resolve = |id: TypeId| {
                result
                    .types
                    .get(id.0)
                    .copied()
                    .map(|id| TypeId(id.0))
                    .ok_or(Refusal::Malformed)
            };
            let ty = match *ty {
                | Type::Arrow(a, b) => {
                    let a = resolve(a)?;
                    let b = resolve(b)?;
                    Type::Arrow(a, b)
                },
                | Type::Lift(inner) => {
                    let inner = resolve(inner)?;
                    Type::Lift(inner)
                },
                | leaf => leaf,
            };
            let id = ContentId(result.records.len());
            result.records.insert(classifier(ty), id);
            result.types.push(id);
        }
        let mut reachable = BTreeSet::new();
        let mut pending = Vec::from([proposal.equation.source, proposal.equation.target]);
        while let Some(id) = pending.pop() {
            budget.spend()?;
            if !reachable.insert(id) {
                continue;
            }
            if let Node::Rigid(term) = proposal.node(id)? {
                pending.extend(term.children().into_iter().flatten());
            }
        }
        for (index, node) in proposal.nodes.iter().enumerate() {
            budget.spend()?;
            let slot = match *node {
                | Node::Point(_) | Node::Predecessor(_) => Slot::Dynamic,
                | Node::Rigid(term) => {
                    let mut children = [Child::Vacant; 3];
                    let mut dynamic = false;
                    for (child, output) in term.children().into_iter().zip(&mut children) {
                        if let Child::Present(child) = child {
                            let child = result.nodes.get(child.0).ok_or(Refusal::Malformed)?;
                            match *child {
                                | Slot::Fixed(id) => *output = Child::Present(TermId(id.0)),
                                | Slot::Dynamic => dynamic = true,
                            }
                        }
                    }
                    if dynamic {
                        Slot::Dynamic
                    }
                    else {
                        let term = result.term_classifier(term)?;
                        let term = term.rebuild(children)?;
                        let record = Node::Rigid(term).record();
                        let fresh = ContentId(result.records.len());
                        let id = *result.records.entry(record).or_insert(fresh);
                        Slot::Fixed(id)
                    }
                },
            };
            if matches!(slot, Slot::Dynamic) && reachable.contains(&TermId(index)) {
                result.plan.push(TermId(index));
            }
            result.nodes.push(slot);
        }
        Ok(result)
    }

    /// Replace a term's classifier coordinate by exact classifier content.
    ///
    /// # Specification
    /// - ensures: preserves term constructors and all nonclassifier payloads.
    /// - fails: malformed classifier reference.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::Malformed`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — numeric classifier coordinates never decide
    ///   agreement.
    /// - witness: `admission::tests::classifier_coordinates_are_not_content`
    fn term_classifier(
        &self,
        term: Term,
    ) -> Result<Term, Refusal>
    {
        let resolve = |id: TypeId| {
            self.types
                .get(id.0)
                .copied()
                .map(|id| TypeId(id.0))
                .ok_or(Refusal::Malformed)
        };
        Ok(match term {
            | Term::Code(ty) => {
                let ty = resolve(ty)?;
                Term::Code(ty)
            },
            | Term::Lambda(ty, body) => {
                let ty = resolve(ty)?;
                Term::Lambda(ty, body)
            },
            | Term::Eliminate(body, ty) => {
                let ty = resolve(ty)?;
                Term::Eliminate(body, ty)
            },
            | term => term,
        })
    }

    /// Resolve fixed content or the already-computed dynamic dependency.
    ///
    /// # Specification
    /// - ensures: returns an exact content coordinate in this member namespace.
    /// - fails: malformed or missing dependency.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Refusal::Malformed`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — predecessor and repeated-point sides remain exact.
    /// - witness: `admission::tests::successor_and_transparency`
    fn resolve(
        &self,
        id: TermId,
        dynamic: &BTreeMap<TermId, ContentId>,
    ) -> Result<ContentId, Refusal>
    {
        let slot = self.nodes.get(id.0).ok_or(Refusal::Malformed)?;
        match *slot {
            | Slot::Fixed(content) => Ok(content),
            | Slot::Dynamic => dynamic.get(&id).copied().ok_or(Refusal::Malformed),
        }
    }
}

/// Resolve one point's validated guard to its fixed body coordinate.
///
/// # Specification
/// - ensures: returns the selected schema-owned arm.
/// - fails: malformed guard table or missing selection.
/// - panics: none.
///
/// # Errors
/// Returns a named point refusal.
///
/// # Adequacy
/// - hypothesis: L3 — unknown and correlated arms cannot bypass row validation.
/// - witness: `admission::tests::schema_and_instance_refusals`
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

/// Intern consumer classifiers once, rejecting foreign classifier content.
///
/// # Specification
/// - ensures: every returned id belongs to the schema's exact vocabulary.
/// - fails: classifier mismatch, malformed arena or exhausted work.
/// - panics: none.
///
/// # Errors
/// Returns `Refusal::ClassifierMismatch` or syntax/fuel failure.
///
/// # Adequacy
/// - hypothesis: L3 — same numeric type id in different arenas is no evidence.
/// - witness: `admission::tests::classifier_coordinates_are_not_content`
fn import_type(
    prepared: &Prepared,
    arena: &Arena,
    root: TypeId,
    known: &mut BTreeMap<TypeId, ContentId>,
    budget: &mut Budget,
    work: &mut Work,
) -> Result<ContentId, Refusal>
{
    let mut pending = Vec::from([(root, false)]);
    while let Some((id, ready)) = pending.pop() {
        if known.contains_key(&id) {
            continue;
        }
        budget.spend()?;
        let ty = arena.ty(id)?;
        if !ready {
            pending.push((id, true));
            match ty {
                | Type::Arrow(a, b) => pending.extend([(a, false), (b, false)]),
                | Type::Lift(inner) => pending.push((inner, false)),
                | _ => {},
            }
            continue;
        }
        let resolve = |id: TypeId| {
            known
                .get(&id)
                .copied()
                .map(|id| TypeId(id.0))
                .ok_or(Refusal::Malformed)
        };
        let ty = match ty {
            | Type::Arrow(a, b) => {
                let a = resolve(a)?;
                let b = resolve(b)?;
                Type::Arrow(a, b)
            },
            | Type::Lift(inner) => {
                let inner = resolve(inner)?;
                Type::Lift(inner)
            },
            | leaf => leaf,
        };
        let content = *prepared
            .records
            .get(&classifier(ty))
            .ok_or(Refusal::ClassifierMismatch)?;
        known.insert(id, content);
        work.0 = work.0.saturating_add(1);
    }
    known.get(&root).copied().ok_or(Refusal::Malformed)
}

/// Compare instantiated content to materialized sides in one exact namespace.
///
/// # Specification
/// - ensures: equality is exact record interning, never hash agreement; no
///   member term or reduct is built. Each materialized node is interned once.
/// - fails: side/classifier mismatch, malformed input or exhausted work.
/// - panics: none.
/// - intension: evaluates only the dependent plan, then walks distinct consumer
///   term and classifier nodes. Ordered-map lookups add logarithmic CPU cost.
///
/// # Errors
/// Returns `Refusal` without an equation verdict on mismatch.
///
/// # Adequacy
/// - hypothesis: L2/L3 — replay, changed sides and cross-arena classifiers
///   distinguish content identity from unchecked ids or projected syntax.
/// - witness: `admission::tests::schema_and_instance_refusals`
/// - witness: `admission::tests::successor_and_transparency`
/// - witness: `admission::tests::classifier_coordinates_are_not_content`
pub(super) fn compare(
    schema: &Schema,
    guards: &[Guard],
    arena: &Arena,
    sides: [TermId; 2],
    budget: &mut Budget,
    mut work: Admission,
) -> Result<Admission, Refusal>
{
    let prepared = &schema.content;
    let mut overlay = Overlay {
        fixed: prepared,
        records: BTreeMap::new(),
    };
    let mut dynamic = BTreeMap::new();
    for id in &prepared.plan {
        budget.spend()?;
        let node = schema.proposal.node(*id)?;
        let term = match node {
            | Node::Point(point) => {
                let arm = arm(schema, guards, point)?;
                dynamic.insert(*id, prepared.resolve(arm, &dynamic)?);
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
            | Node::Rigid(term) => {
                let mut children = [Child::Vacant; 3];
                for (child, output) in term.children().into_iter().zip(&mut children) {
                    if let Child::Present(child) = child {
                        let child = prepared.resolve(child, &dynamic)?;
                        *output = Child::Present(TermId(child.0));
                    }
                }
                let term = prepared.term_classifier(term)?;
                term.rebuild(children)?
            },
        };
        dynamic.insert(*id, overlay.intern(Node::Rigid(term).record()));
        work.instantiations.0 = work.instantiations.0.saturating_add(1);
    }
    let mut known = BTreeMap::new();
    let mut types = BTreeMap::new();
    let mut pending: Vec<_> = sides.into_iter().map(|id| (id, false)).collect();
    while let Some((id, ready)) = pending.pop() {
        if known.contains_key(&id) {
            continue;
        }
        budget.spend()?;
        let term = arena.term(id)?;
        if !ready {
            pending.push((id, true));
            pending.extend(term.children().into_iter().flatten().map(|id| (id, false)));
            continue;
        }
        let term = match term {
            | Term::Code(ty) => {
                let ty = import_type(
                    prepared,
                    arena,
                    ty,
                    &mut types,
                    budget,
                    &mut work.classifiers,
                )?;
                Term::Code(TypeId(ty.0))
            },
            | Term::Lambda(ty, body) => {
                let ty = import_type(
                    prepared,
                    arena,
                    ty,
                    &mut types,
                    budget,
                    &mut work.classifiers,
                )?;
                Term::Lambda(TypeId(ty.0), body)
            },
            | Term::Eliminate(body, ty) => {
                let ty = import_type(
                    prepared,
                    arena,
                    ty,
                    &mut types,
                    budget,
                    &mut work.classifiers,
                )?;
                Term::Eliminate(body, TypeId(ty.0))
            },
            | term => term,
        };
        let mut children = [Child::Vacant; 3];
        for (child, output) in term.children().into_iter().zip(&mut children) {
            if let Child::Present(child) = child {
                let child: ContentId = *known.get(&child).ok_or(Refusal::Malformed)?;
                *output = Child::Present(TermId(child.0));
            }
        }
        let term = term.rebuild(children)?;
        known.insert(id, overlay.intern(Node::Rigid(term).record()));
        work.comparisons.0 = work.comparisons.0.saturating_add(1);
    }
    for (expected, actual) in [
        schema.proposal.equation.source,
        schema.proposal.equation.target,
    ]
    .into_iter()
    .zip(sides)
    {
        if prepared.resolve(expected, &dynamic)? != *known.get(&actual).ok_or(Refusal::Malformed)? {
            return Err(Refusal::SidesMismatch);
        }
    }
    Ok(work)
}
