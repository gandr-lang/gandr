//! Flat, content-interned syntax for staging equation families.

mod serialization;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Model;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;
use gandr_theory_deep_inference::ArmAddress;
use gandr_theory_deep_inference::EntryIndex;
use gandr_theory_deep_inference::NodeCount;

/// An address in a pattern graph, distinct from a staging arena address.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize)]
pub(super) struct Id(pub usize);

/// A constructor's nonrecursive payload, including opaque template points.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Head
{
    /// Ordinary de Bruijn variable.
    Variable(Index),
    /// Meta natural.
    OuterNatural(Natural),
    /// Object natural.
    InnerNatural(Model, Natural),
    /// Type code.
    Code(TypeId),
    /// Binder domain.
    Lambda(TypeId),
    /// Function application.
    Apply,
    /// Residual multiplication.
    Multiply,
    /// Object quotation.
    Quote,
    /// Meta splice.
    Splice,
    /// Natural iteration.
    Iterate,
    /// Identity elimination's classifier.
    Eliminate(TypeId),
    /// One jointly generalized occurrence column.
    Point(EntryIndex),
    /// Producer-only predecessor of the source's outer-numeral point.
    Predecessor,
}

/// Fixed-capacity children; unused slots are absent, not sentinel addresses.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize)]
pub(super) struct Children(pub [Option<Id>; 3]);

/// One flat constructor node.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize)]
pub(super) struct Node
{
    /// Constructor and rigid payload.
    pub head: Head,
    /// Edges to earlier nodes.
    pub children: Children,
}

/// Pattern content, with copied classifiers but no member certificates.
///
/// # Specification
/// - ensures: interning, unfolded sizes and build-local cache addresses name
///   the same nodes; children refer only to earlier nodes. Classifiers are
///   interned by content rather than input-arena coordinates.
/// - panics: none.
/// - executable: none — this private aggregate has no call to instrument;
///   intern, import and compact check its relationships at their boundaries.
///
/// # Adequacy
/// - hypothesis: L2/L3 — finite reconstructed equations, exact cancellation
///   prices and two different classifier vocabularies expose lost edges,
///   occurrence undercharging and arena-coordinate cache aliasing.
/// - witness: `template::tests::serialized_images_reconstruct_the_original_equations`
/// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `template::tests::cache_keys_include_classifier_content`
#[derive(Clone, Debug, Default)]
pub(super) struct Graph
{
    /// Interned nodes in dependency order.
    nodes: Vec<Node>,
    /// Exact interning; hashes never establish equality.
    ids: BTreeMap<Node, Id>,
    /// Tree node counts, saturating at the machine boundary.
    sizes: Vec<NodeCount>,
    /// Bottom-up addresses for inheritance-cache keys only.
    addresses: Vec<ArmAddress>,
    /// Canonical classifier vocabulary used by these nodes.
    types: BTreeMap<TypeId, Type>,
    /// Exact classifier interning, independent of source-arena coordinates.
    type_ids: BTreeMap<Type, TypeId>,
}

impl Head
{
    /// Read a staging constructor without its edges.
    ///
    /// # Specification
    /// trivial.
    fn of(term: Term) -> Self
    {
        match term {
            | Term::Variable(index) => Self::Variable(index),
            | Term::Natural(Stage::Outer, value) => Self::OuterNatural(value),
            | Term::Natural(Stage::Inner(model), value) => Self::InnerNatural(model, value),
            | Term::Code(ty) => Self::Code(ty),
            | Term::Lambda(ty, _) => Self::Lambda(ty),
            | Term::Apply(..) => Self::Apply,
            | Term::Multiply(..) => Self::Multiply,
            | Term::Quote(_) => Self::Quote,
            | Term::Splice(_) => Self::Splice,
            | Term::Iterate(..) => Self::Iterate,
            | Term::Eliminate(_, ty) => Self::Eliminate(ty),
        }
    }
}

impl Graph
{
    /// Address classifier content as part of the region, not arena coordinates
    /// alone.
    ///
    /// # Specification
    /// - ensures: every classifier constructor and payload contributes to the
    ///   region key; hashing remains build-local and is not equality evidence.
    /// - panics: none.
    /// - executable: none — the non-injective build-local digest has no
    ///   inverse; classifier separation is observed through cache behavior.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal term shapes over different binder domains do
    ///   not reuse inheritance evidence solely because both domains have ID
    ///   zero.
    /// - witness: `template::tests::cache_keys_include_classifier_content`
    pub(super) fn vocabulary_address(&self) -> ArmAddress
    {
        let mut address = ArmAddress::of(&"stage.classifiers.v1");
        for (id, ty) in &self.types {
            let tag = core::mem::discriminant(ty);
            address = match *ty {
                | Type::In(model) | Type::Universe(model) => {
                    ArmAddress::of(&(address, id, tag, model))
                },
                | Type::Nat(stage) => {
                    let model = match stage {
                        | Stage::Outer => Model(0),
                        | Stage::Inner(model) => model,
                    };
                    ArmAddress::of(&(address, id, tag, core::mem::discriminant(&stage), model))
                },
                | Type::Arrow(a, b) => ArmAddress::of(&(address, id, tag, a, b)),
                | Type::Lift(inner) => ArmAddress::of(&(address, id, tag, inner)),
            };
        }
        address
    }

    /// Allocate pairwise distinct opaque constants outside the input
    /// vocabulary.
    ///
    /// # Specification
    /// - ensures: each unbound point gets a fresh model-token code, different
    ///   from every model mentioned in this graph and from every other point.
    /// - fails: Overflow if the finite model namespace is exhausted; arena
    ///   errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Overflow` or classifier allocation errors.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a model at the largest representable index and two
    ///   points distinguish fixed-sentinel collision from fresh rigid
    ///   constants.
    /// - witness: `template::tests::skolems_are_fresh_and_pairwise_distinct`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|skolems|
        skolems.iter().all(|(id, ty)| skolems.range(..id).all(|(_, previous)| previous != ty)
            && matches!(arena.ty(*ty), Ok(Type::In(_))))))]
    fn skolems(
        &self,
        arena: &mut Arena,
        bindings: &BTreeMap<EntryIndex, Id>,
    ) -> Result<BTreeMap<Id, TypeId>, StageError>
    {
        let points = self
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match node.head {
                | Head::Point(point) if !bindings.contains_key(&point) => Some(Id(index)),
                | Head::Predecessor if node.children.0.first().copied().flatten()
                    .and_then(|id| self.nodes.get(id.0))
                    .is_some_and(|child| matches!(child.head, Head::Point(point) if !bindings.contains_key(&point))) => Some(Id(index)),
                | _ => None,
            })
            .collect::<BTreeSet<_>>();
        if points.is_empty() {
            return Ok(BTreeMap::new());
        }
        let mut occupied = BTreeSet::new();
        for ty in self.types.values() {
            match *ty {
                | Type::In(model) | Type::Universe(model) | Type::Nat(Stage::Inner(model)) => {
                    occupied.insert(model);
                },
                | Type::Nat(Stage::Outer) | Type::Arrow(..) | Type::Lift(_) => {},
            }
        }
        for node in &self.nodes {
            if let Head::InnerNatural(model, _) = node.head {
                occupied.insert(model);
            }
        }
        let mut cursor = usize::MAX;
        let mut skolems = BTreeMap::new();
        for point in points {
            while occupied.contains(&Model(cursor)) {
                cursor = cursor.checked_sub(1).ok_or(StageError::Overflow)?;
            }
            let model = Model(cursor);
            occupied.insert(model);
            let ty = arena.alloc_type(Type::In(model))?;
            skolems.insert(point, ty);
        }
        Ok(skolems)
    }

    /// Start a one-member scratch graph with the same classifier vocabulary.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn member(&self) -> Self
    {
        Self {
            types: self.types.clone(),
            type_ids: self.type_ids.clone(),
            ..Self::default()
        }
    }

    /// Compare content exactly across graphs sharing a classifier vocabulary.
    ///
    /// # Specification
    /// - ensures: succeeds exactly when both rooted constructor trees agree.
    /// - fails: `InvalidCertificate` for unequal content; Unbalanced for bad
    ///   IDs.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::InvalidCertificate` or `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — matching selects exact existing arms and refuses
    ///   different numerals even when constructor skeletons agree.
    /// - witness: `template::tests::peak_choices_are_correlated`
    #[spec(ensures: |output| output.is_err() || self.node(left).ok().zip(other.node(right).ok())
        .is_some_and(|(left, right)| left.head == right.head))]
    pub(super) fn compare(
        &self,
        left: Id,
        other: &Self,
        right: Id,
    ) -> Result<(), StageError>
    {
        let mut pending = Vec::from([(left, right)]);
        let mut seen = BTreeSet::new();
        while let Some((left, right)) = pending.pop() {
            if !seen.insert((left, right)) {
                continue;
            }
            let left = self.node(left)?;
            let right = other.node(right)?;
            if left.head != right.head {
                return Err(StageError::InvalidCertificate);
            }
            pending.extend(
                left.children
                    .0
                    .into_iter()
                    .flatten()
                    .zip(right.children.0.into_iter().flatten()),
            );
        }
        Ok(())
    }

    /// Resolve a checked pattern coordinate.
    ///
    /// # Specification
    /// - ensures: returns the node at the supplied coordinate.
    /// - fails: Unbalanced for an absent coordinate.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — projection of harvested equations checks every edge.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::projection_rejects_missing_graph_edges_and_invalid_predecessors`
    #[spec(ensures: |output| output == self.nodes.get(id.0).copied().ok_or(StageError::Unbalanced))]
    pub(super) fn node(
        &self,
        id: Id,
    ) -> Result<Node, StageError>
    {
        self.nodes.get(id.0).copied().ok_or(StageError::Unbalanced)
    }

    /// Return a pattern's unfolded node count.
    ///
    /// # Specification
    /// - ensures: returns the unfolded count, saturated at the machine bound.
    /// - fails: Unbalanced for an absent coordinate.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — independent tree counts detect lost occurrences.
    /// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
    /// - witness: `template::tests::projection_rejects_missing_graph_edges_and_invalid_predecessors`
    #[spec(ensures: |output| output == self.sizes.get(id.0).copied().ok_or(StageError::Unbalanced))]
    pub(super) fn size(
        &self,
        id: Id,
    ) -> Result<NodeCount, StageError>
    {
        self.sizes.get(id.0).copied().ok_or(StageError::Unbalanced)
    }

    /// Return a pattern's cache address.
    ///
    /// # Specification
    /// - ensures: returns the bottom-up content address for a live node.
    /// - fails: Unbalanced for an absent coordinate.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated arms reuse exactly their content triples.
    /// - witness: `template::tests::the_inheritance_check_runs_once_per_distinct_triple`
    /// - witness: `template::tests::projection_rejects_missing_graph_edges_and_invalid_predecessors`
    #[spec(ensures: |output| output == self.addresses.get(id.0).copied().ok_or(StageError::Unbalanced))]
    pub(super) fn address(
        &self,
        id: Id,
    ) -> Result<ArmAddress, StageError>
    {
        self.addresses
            .get(id.0)
            .copied()
            .ok_or(StageError::Unbalanced)
    }

    /// Intern one constructor over earlier nodes.
    ///
    /// # Specification
    /// - ensures: structurally equal nodes share an address; size sums
    ///   children.
    /// - fails: Unbalanced for a missing child.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — exact projection and independent size observers
    ///   distinguish dropped children and accidental arm identification.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::a_template_is_emitted_only_below_its_expansion_factor`
    /// - witness: `template::tests::projection_rejects_missing_graph_edges_and_invalid_predecessors`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|id|
        self.nodes.get(id.0) == Some(&node) && self.ids.get(&node) == Some(id)
            && self.sizes.get(id.0).is_some_and(|size| usize::from(*size) >= 1)))]
    pub(super) fn intern(
        &mut self,
        node: Node,
    ) -> Result<Id, StageError>
    {
        if let Some(id) = self.ids.get(&node) {
            return Ok(*id);
        }
        let mut size = 1_usize;
        let mut addresses = [None; 3];
        for (child, address) in node.children.0.iter().zip(&mut addresses) {
            if let Some(child) = *child {
                let child_address = self.address(child)?;
                *address = Some(child_address);
                let child_size = self.size(child)?;
                size = size.saturating_add(usize::from(child_size));
            }
        }
        let id = Id(self.nodes.len());
        self.nodes.push(node);
        self.ids.insert(node, id);
        self.sizes.push(NodeCount::from(size));
        self.addresses.push(ArmAddress::of(&(node.head, addresses)));
        Ok(id)
    }

    /// Copy all classifier dependencies of a term payload.
    ///
    /// # Specification
    /// - ensures: the graph retains each referenced classifier and its
    ///   children.
    /// - fails: the arena's `UnknownType` on a malformed payload.
    /// - panics: none.
    ///
    /// # Errors
    /// Propagates `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — typed replay of exported programs detects lost types.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|id| self.types.contains_key(id)))]
    fn import_type(
        &mut self,
        arena: &Arena,
        root: TypeId,
    ) -> Result<TypeId, StageError>
    {
        let mut pending = Vec::from([(root, false)]);
        let mut known = BTreeMap::new();
        while let Some((id, ready)) = pending.pop() {
            if known.contains_key(&id) {
                continue;
            }
            let ty = arena.ty(id)?;
            if !ready {
                pending.push((id, true));
                match ty {
                    | Type::Arrow(a, b) => pending.extend([(a, false), (b, false)]),
                    | Type::Lift(inner) => pending.push((inner, false)),
                    | Type::In(_) | Type::Universe(_) | Type::Nat(_) => {},
                }
                continue;
            }
            let ty = match ty {
                | Type::Arrow(a, b) => {
                    let a = *known.get(&a).ok_or(StageError::Unbalanced)?;
                    let b = *known.get(&b).ok_or(StageError::Unbalanced)?;
                    Type::Arrow(a, b)
                },
                | Type::Lift(inner) => {
                    let inner = *known.get(&inner).ok_or(StageError::Unbalanced)?;
                    Type::Lift(inner)
                },
                | leaf @ (Type::In(_) | Type::Universe(_) | Type::Nat(_)) => leaf,
            };
            let target = if let Some(id) = self.type_ids.get(&ty) {
                *id
            }
            else {
                let target = TypeId(self.types.len());
                self.types.insert(target, ty);
                self.type_ids.insert(ty, target);
                target
            };
            known.insert(id, target);
        }
        known.get(&root).copied().ok_or(StageError::Unbalanced)
    }

    /// Import roots jointly, preserving exact repeated subterm content.
    ///
    /// # Specification
    /// - ensures: outputs correspond in order to the supplied roots.
    /// - fails: malformed arena lookups or internal missing dependencies.
    /// - panics: none.
    /// - intension: each reachable arena node is visited once per import.
    ///
    /// # Errors
    /// Returns `UnknownTerm`, `UnknownType` or Unbalanced.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent replay and side-size counting distinguish
    ///   root order, binder payload and subtree loss.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::empty_and_malformed_families_preserve_refusals`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|ids|
        ids.len() == roots.len() && ids.iter().all(|id| self.nodes.get(id.0).is_some())))]
    pub(super) fn import(
        &mut self,
        arena: &Arena,
        roots: &[TermId],
    ) -> Result<Vec<Id>, StageError>
    {
        let mut known = BTreeMap::new();
        let mut pending: Vec<_> = roots.iter().rev().map(|root| (*root, false)).collect();
        while let Some((id, ready)) = pending.pop() {
            if known.contains_key(&id) {
                continue;
            }
            let term = arena.term(id)?;
            if !ready {
                pending.push((id, true));
                pending.extend(
                    term.children()
                        .into_iter()
                        .flatten()
                        .rev()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let head = match Head::of(term) {
                | Head::Code(ty) => {
                    let ty = self.import_type(arena, ty)?;
                    Head::Code(ty)
                },
                | Head::Lambda(ty) => {
                    let ty = self.import_type(arena, ty)?;
                    Head::Lambda(ty)
                },
                | Head::Eliminate(ty) => {
                    let ty = self.import_type(arena, ty)?;
                    Head::Eliminate(ty)
                },
                | head => head,
            };
            let mut children = Children([None; 3]);
            for (source, target) in term.children().into_iter().zip(&mut children.0) {
                if let Child::Present(source) = source {
                    *target = Some(*known.get(&source).ok_or(StageError::Unbalanced)?);
                }
            }
            let node = self.intern(Node { head, children })?;
            known.insert(id, node);
        }
        roots
            .iter()
            .map(|root| known.get(root).copied().ok_or(StageError::Unbalanced))
            .collect()
    }

    /// Export the retained classifiers into an independent replay arena.
    ///
    /// # Specification
    /// - ensures: returns a mapping for every retained classifier.
    /// - fails: Unbalanced if a dependency is missing; propagates allocation
    ///   errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns stage allocation errors or Unbalanced.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent typed replay detects wrong classifier
    ///   edges.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|types|
        types.len() == self.types.len() && self.types.keys().all(|id| types.contains_key(id))
            && types.values().all(|id| arena.ty(*id).is_ok())))]
    fn export_types(
        &self,
        arena: &mut Arena,
    ) -> Result<BTreeMap<TypeId, TypeId>, StageError>
    {
        let mut known = BTreeMap::new();
        for (id, ty) in &self.types {
            let ty = match *ty {
                | Type::Arrow(a, b) => Type::Arrow(
                    *known.get(&a).ok_or(StageError::Unbalanced)?,
                    *known.get(&b).ok_or(StageError::Unbalanced)?,
                ),
                | Type::Lift(inner) => {
                    Type::Lift(*known.get(&inner).ok_or(StageError::Unbalanced)?)
                },
                | leaf @ (Type::In(_) | Type::Universe(_) | Type::Nat(_)) => leaf,
            };
            known.insert(*id, arena.alloc_type(ty)?);
        }
        Ok(known)
    }

    /// Materialize roots with selected arms; other points become rigid
    /// constants.
    ///
    /// # Specification
    /// - ensures: each point selects its supplied arm, or a distinct opaque
    ///   code constant. Constants cannot be read as lambdas, naturals or
    ///   splices.
    /// - fails: Unbalanced on missing dependencies; propagates arena errors.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns stage allocation errors, Overflow or Unbalanced.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — concrete projection agrees with replay; a guard at
    ///   a discriminated head blocks inheritance with other points rigid.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::an_entry_a_decision_discriminates_on_yields_no_template`
    /// - witness: `template::tests::projection_rejects_missing_graph_edges_and_invalid_predecessors`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|ids|
        ids.len() == roots.len() && ids.iter().all(|id| arena.term(*id).is_ok())))]
    pub(super) fn export(
        &self,
        arena: &mut Arena,
        roots: &[Id],
        bindings: &BTreeMap<EntryIndex, Id>,
    ) -> Result<Vec<TermId>, StageError>
    {
        let types = self.export_types(arena)?;
        let skolems = self.skolems(arena, bindings)?;
        let mut known = BTreeMap::new();
        let mut pending: Vec<_> = roots.iter().rev().map(|root| (*root, false)).collect();
        while let Some((id, ready)) = pending.pop() {
            if known.contains_key(&id) {
                continue;
            }
            let node = self.node(id)?;
            if let Head::Point(entry) = node.head {
                if let Some(body) = bindings.get(&entry) {
                    if let Some(value) = known.get(body) {
                        known.insert(id, *value);
                    }
                    else {
                        pending.push((id, true));
                        pending.push((*body, false));
                    }
                }
                else {
                    let ty = *skolems.get(&id).ok_or(StageError::Unbalanced)?;
                    let value = arena.alloc(Term::Code(ty))?;
                    known.insert(id, value);
                }
                continue;
            }
            if !ready {
                pending.push((id, true));
                pending.extend(
                    node.children
                        .0
                        .into_iter()
                        .flatten()
                        .rev()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let mut children = [Child::Vacant; 3];
            for (source, target) in node.children.0.into_iter().zip(&mut children) {
                if let Some(source) = source {
                    *target = Child::Present(*known.get(&source).ok_or(StageError::Unbalanced)?);
                }
            }
            if node.head == Head::Predecessor {
                let point = node
                    .children
                    .0
                    .first()
                    .copied()
                    .flatten()
                    .ok_or(StageError::Unbalanced)?;
                let Head::Point(entry) = self.node(point)?.head
                else {
                    return Err(StageError::Unbalanced);
                };
                let term = if bindings.contains_key(&entry) {
                    let value = *known.get(&point).ok_or(StageError::Unbalanced)?;
                    let Term::Natural(Stage::Outer, Natural(value)) = arena.term(value)?
                    else {
                        return Err(StageError::InvalidCertificate);
                    };
                    let value = value.checked_sub(1).ok_or(StageError::InvalidCertificate)?;
                    Term::Natural(Stage::Outer, Natural(value))
                }
                else {
                    let ty = *skolems.get(&id).ok_or(StageError::Unbalanced)?;
                    Term::Code(ty)
                };
                let value = arena.alloc(term)?;
                known.insert(id, value);
                continue;
            }
            let dummy = TermId(0);
            let term = match node.head {
                | Head::Variable(index) => Term::Variable(index),
                | Head::OuterNatural(value) => Term::Natural(Stage::Outer, value),
                | Head::InnerNatural(model, value) => Term::Natural(Stage::Inner(model), value),
                | Head::Code(ty) => Term::Code(*types.get(&ty).ok_or(StageError::Unbalanced)?),
                | Head::Lambda(ty) => {
                    Term::Lambda(*types.get(&ty).ok_or(StageError::Unbalanced)?, dummy)
                },
                | Head::Apply => Term::Apply(dummy, dummy),
                | Head::Multiply => Term::Multiply(dummy, dummy),
                | Head::Quote => Term::Quote(dummy),
                | Head::Splice => Term::Splice(dummy),
                | Head::Iterate => Term::Iterate(dummy, dummy, dummy),
                | Head::Eliminate(ty) => {
                    Term::Eliminate(dummy, *types.get(&ty).ok_or(StageError::Unbalanced)?)
                },
                | Head::Point(_) | Head::Predecessor => return Err(StageError::Unbalanced),
            };
            let term = term.rebuild(children)?;
            known.insert(id, arena.alloc(term)?);
        }
        roots
            .iter()
            .map(|root| known.get(root).copied().ok_or(StageError::Unbalanced))
            .collect()
    }

    /// Retain only the skeleton and distinct arms, releasing all other members.
    ///
    /// # Specification
    /// - ensures: the returned graph contains exactly roots and their
    ///   descendants; the map translates every retained node without changing
    ///   content.
    /// - fails: Unbalanced for an absent node.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — projection after compaction preserves every member.
    /// - witness: `template::tests::every_member_admits_as_its_plain_replay`
    /// - witness: `template::tests::projection_rejects_missing_graph_edges_and_invalid_predecessors`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|pair|
        pair.0.nodes.len() == pair.1.len() && roots.iter().all(|root| pair.1.contains_key(root))
            && pair.1.values().all(|id| pair.0.nodes.get(id.0).is_some())))]
    pub(super) fn compact(
        &self,
        roots: &[Id],
    ) -> Result<(Self, BTreeMap<Id, Id>), StageError>
    {
        let mut retained = BTreeSet::new();
        let mut pending = roots.to_vec();
        while let Some(id) = pending.pop() {
            if retained.insert(id) {
                pending.extend(self.node(id)?.children.0.into_iter().flatten());
            }
        }
        let mut graph = Self {
            types: self.types.clone(),
            type_ids: self.type_ids.clone(),
            ..Self::default()
        };
        let mut map = BTreeMap::new();
        for id in retained {
            let mut node = self.node(id)?;
            for child in node.children.0.iter_mut().flatten() {
                *child = *map.get(child).ok_or(StageError::Unbalanced)?;
            }
            map.insert(id, graph.intern(node)?);
        }
        Ok((graph, map))
    }
}
