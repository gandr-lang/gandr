//! Co-de Bruijn support: compact nodes, edge thinnings and root placements.
//!
//! A thinning lists selected indices, innermost first, independently in both
//! zones. An edge targets its parent's compact scope, extended by index zero
//! when that child binds. Its selections record both the cover and binder use.

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    warn(
        specification_present,
        spec_attribute_present,
        adequacy_present,
        adequacy_block_grammar
    )
)]

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::hash::Hash as _;
use core::hash::Hasher as _;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::NodeIndex;
use crate::content::ContentNode;
use crate::content::Opacity;
use crate::content::Sort;
use crate::content::map_node;
use crate::region::Reference;

/// An order-preserving selection from an ambient two-zone scope.
///
/// # Specification
/// - ensures: each zone's indices are strictly ascending; omitted binders
///   contribute neither a variable nor a table identity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — relocation under unused binders, distinct variable wiring
///   and independent zones distinguish dropped or conflated selections.
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Thinning
{
    /// Selected intuitionistic indices.
    intuitionistic: Vec<DeBruijnIndex>,
    /// Selected linear indices.
    linear: Vec<DeBruijnIndex>,
}

impl Thinning
{
    /// Assemble the decoder's two strictly ascending selections.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_indices(
        intuitionistic: Vec<DeBruijnIndex>,
        linear: Vec<DeBruijnIndex>,
    ) -> Self
    {
        Self {
            intuitionistic,
            linear,
        }
    }

    /// The indices selected in `zone`, innermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn indices(
        &self,
        zone: Zone,
    ) -> &[DeBruijnIndex]
    {
        match zone {
            | Zone::Intuitionistic => &self.intuitionistic,
            | Zone::Linear => &self.linear,
        }
    }

    /// The compact scope this selection embeds.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn scope(&self) -> Scope
    {
        Scope {
            intuitionistic: BinderDepth::from(self.intuitionistic.len()),
            linear: BinderDepth::from(self.linear.len()),
        }
    }
}

/// The number of actually used binders in each zone of a compact node.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Scope
{
    /// The intuitionistic width.
    intuitionistic: BinderDepth,
    /// The linear width.
    linear: BinderDepth,
}

impl Scope
{
    /// Assemble decoded scope widths, checked against a cover before use.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        intuitionistic: BinderDepth,
        linear: BinderDepth,
    ) -> Self
    {
        Self {
            intuitionistic,
            linear,
        }
    }

    /// The number of used binders in `zone`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn depth(
        self,
        zone: Zone,
    ) -> BinderDepth
    {
        match zone {
            | Zone::Intuitionistic => self.intuitionistic,
            | Zone::Linear => self.linear,
        }
    }
}

/// One relocatable former, its cover and its exact syntactic references.
///
/// # Specification
/// - ensures: a variable carries unit, not an ambient index; `cover` embeds
///   each child's whole support into this node's scope plus its local binder.
///   Every free slot is selected by some child. Reference sets include exactly
///   occurrences below the node, classified by whether a type former encloses
///   them; a reference can occur in both positions.
/// - provides: content identity independent of unused ambient binders.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — an independent arena walk observes reference exactness;
///   L3 — relocation and altered wiring separate support from cached indices.
/// - witness: `tests::incremental::carried_footprint_matches_reference_walk`
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SupportedNode
{
    /// A former whose variables are bare leaves of their zone.
    former: ContentNode<()>,
    /// One thinning per child, in former order.
    cover: Vec<Thinning>,
    /// The minimal free scope.
    scope: Scope,
    /// References in value positions, outside every type former.
    value_reads: BTreeSet<Reference>,
    /// References beneath a type former.
    type_reads: BTreeSet<Reference>,
    /// Whether this subtree contains an unresolved arena node.
    opacity: Opacity,
}

impl SupportedNode
{
    /// Assemble decoded fields, validated together before the table escapes.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_parts(
        former: ContentNode<()>,
        cover: Vec<Thinning>,
        scope: Scope,
        value_reads: BTreeSet<Reference>,
        type_reads: BTreeSet<Reference>,
    ) -> Self
    {
        Self {
            former,
            cover,
            scope,
            value_reads,
            type_reads,
            opacity: Opacity::Transparent,
        }
    }

    /// The node's former in its minimal scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn former(&self) -> &ContentNode<()>
    {
        &self.former
    }

    /// The child embeddings, in former order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cover(&self) -> &[Thinning]
    {
        &self.cover
    }

    /// The minimal two-zone scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> Scope
    {
        self.scope
    }

    /// References occurring outside type formers, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value_reads(&self) -> impl ExactSizeIterator<Item = &Reference>
    {
        self.value_reads.iter()
    }

    /// References occurring beneath type formers, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn type_reads(&self) -> impl ExactSizeIterator<Item = &Reference>
    {
        self.type_reads.iter()
    }

    /// Whether the subtree resolves completely.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn opacity(&self) -> Opacity
    {
        self.opacity
    }

    /// The former's sort.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn sort(&self) -> Sort
    {
        self.former.sort()
    }

    /// The former's children and their required sorts.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn children(&self) -> crate::content::Children
    {
        self.former.children()
    }
}

quenchant_shape::reason_enum! {
    /// Why compact support cannot be projected into ambient de Bruijn indices.
    pub mod expansion {
        /// The reason no de Bruijn view is returned.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A binder shifts an ambient index beyond the index representation.
            IndexOverflow,
        }
    }
}

/// A compact node placed in an ambient scope.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Placed
{
    /// The compact table entry.
    pub node: NodeIndex,
    /// Its support in the ambient scope.
    pub thinning: Thinning,
}

/// How a child crosses an intuitionistic binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Binding
{
    /// No binder is introduced.
    Free,
    /// Index zero is bound; outer indices shift by one.
    Bound,
}

/// The child position within a former.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ChildSlot(pub usize);

/// Whether `slot` of `node` introduces an intuitionistic binder.
///
/// # Specification
/// - ensures: lambda bodies, bind continuations, case branches and dependent Pi
///   codomains bind once; every other child, including static Pi, binds none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — all binding formers and static Pi's non-binding codomain
///   are separated by exact reconstructed indices and minimal scopes.
/// - witness: `content::tests::covers_preserve_every_binding_former`
#[spec(ensures: |ret| (ret == Binding::Bound) == match *node {
    ContentNode::Lambda(_) | ContentNode::StaticLambda(_) => slot.0 == 0,
    ContentNode::Bind(..) | ContentNode::Pi { .. } => slot.0 == 1,
    ContentNode::Case { .. } => slot.0 == 1 || slot.0 == 2,
    _ => false,
})]
pub fn binding<Index>(
    node: &ContentNode<Index>,
    slot: ChildSlot,
) -> Binding
{
    match (node, slot.0) {
        | (&ContentNode::Lambda(_) | &ContentNode::StaticLambda(_), 0)
        | (&ContentNode::Bind(..) | &ContentNode::Pi { .. }, 1)
        | (&ContentNode::Case { .. }, 1 | 2) => Binding::Bound,
        | _ => Binding::Free,
    }
}

/// The child support embedded into the parent's minimal scope.
///
/// # Specification
/// - requires: `parent` contains the child's free support outside `under`.
/// - ensures: each child selection becomes its rank in the parent's support; a
///   used bound index stays zero and outer ranks shift past it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — relocating one subterm under distinct unused
///   interleavings separates ambient indices from ranks, with exact expansion
///   as observer.
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
#[spec(ensures: |ret| ret.scope() == child.scope()
    && [Zone::Intuitionistic, Zone::Linear].into_iter().all(|zone|
        ret.indices(zone).windows(2).all(|pair| pair.first() < pair.last())))]
fn embedding(
    child: &Thinning,
    parent: &Thinning,
    under: Binding,
) -> Thinning
{
    let mut result = Thinning::default();
    for (zone, target) in [
        (Zone::Intuitionistic, &mut result.intuitionistic),
        (Zone::Linear, &mut result.linear),
    ] {
        let shift = u32::from(zone == Zone::Intuitionistic && under == Binding::Bound);
        target.reserve(child.indices(zone).len());
        for index in child.indices(zone) {
            let index = u32::from(*index);
            let mapped = if index < shift {
                0
            }
            else {
                let outer = DeBruijnIndex::from(index.saturating_sub(shift));
                // The union contains every child's outer selection. A rank
                // cannot exceed the source index, which already fits u32.
                let rank = parent.indices(zone).partition_point(|held| *held < outer);
                u32::try_from(rank)
                    .unwrap_or(u32::MAX)
                    .saturating_add(shift)
            };
            target.push(DeBruijnIndex::from(mapped));
        }
    }
    result
}

/// Union a child's free support into a parent thinning, dropping its binder.
///
/// # Specification
/// - ensures: exactly the parent selections and child selections outside its
///   binder, in both zones; only intuitionistic indices cross the binder.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — repeated and disjoint selections separate lost support
///   from accidental duplication at a cover.
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
#[spec(captures: before = held.clone(),
    ensures: [Zone::Intuitionistic, Zone::Linear].into_iter().all(|zone| {
        let shift = u32::from(zone == Zone::Intuitionistic && under == Binding::Bound);
        let expected = before.indices(zone).iter().copied().chain(other.indices(zone).iter().filter_map(|index|
            u32::from(*index).checked_sub(shift).map(DeBruijnIndex::from))).collect::<BTreeSet<_>>();
        held.indices(zone).iter().copied().collect::<BTreeSet<_>>() == expected
            && held.indices(zone).windows(2).all(|pair| pair.first() < pair.last())
    }))]
fn join(
    held: &mut Thinning,
    other: &Thinning,
    under: Binding,
)
{
    for (zone, target) in [
        (Zone::Intuitionistic, &mut held.intuitionistic),
        (Zone::Linear, &mut held.linear),
    ] {
        let shift = u32::from(zone == Zone::Intuitionistic && under == Binding::Bound);
        target.extend(other.indices(zone).iter().filter_map(|index| {
            u32::from(*index)
                .checked_sub(shift)
                .map(DeBruijnIndex::from)
        }));
        target.sort_unstable();
        target.dedup();
    }
}

/// Construct exact reference and opacity support from already-built children.
///
/// # Specification
/// - requires: each child resolves in `nodes`.
/// - ensures: reference occurrences are unioned; crossing a type former
///   promotes value occurrences to type occurrences. Opacity propagates upward.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the arena oracle distinguishes lost references and
///   incorrect promotion at quotes and element types; L3 covers shared
///   positions.
/// - witness: `tests::incremental::carried_footprint_matches_reference_walk`
/// - witness: `footprint::tests::type_support_holds_only_type_positions`
#[spec(captures: entry = (former.clone(), cover.clone()),
    ensures: |ret| ret.former == entry.0 && ret.cover == entry.1 && ret.scope == scope
        && (!matches!(ret.former.sort(), Sort::ValueType | Sort::CompType) || ret.value_reads.is_empty())
        && ret.former.children().iter().all(|(child, _)| nodes.get(usize::from(child)).is_none_or(|child|
            child.type_reads.is_subset(&ret.type_reads)
            && child.value_reads.is_subset(if matches!(ret.former.sort(), Sort::ValueType | Sort::CompType)
                { &ret.type_reads } else { &ret.value_reads })))
        && (ret.opacity == Opacity::Opaque) == (matches!(ret.former, ContentNode::Unresolved(_))
            || ret.former.children().iter().any(|(child, _)| nodes.get(usize::from(child)).is_some_and(|child| child.opacity == Opacity::Opaque))))]
pub fn assemble(
    former: ContentNode<()>,
    cover: Vec<Thinning>,
    scope: Scope,
    nodes: &[SupportedNode],
) -> SupportedNode
{
    let (value_reads, type_reads, opacity) = references_of(&former, nodes);
    SupportedNode {
        former,
        cover,
        scope,
        value_reads,
        type_reads,
        opacity,
    }
}

/// Compose value reads, type reads and opacity without copying syntax payloads.
///
/// # Specification
/// - requires: every child resolves in `nodes`.
/// - ensures: the two exact reference sets and propagated opacity; a type
///   former promotes value-position references to type positions.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the independent arena oracle distinguishes omitted reads
///   and false promotion; L3 — forged persisted reference sets are rejected.
/// - witness: `tests::incremental::carried_footprint_matches_reference_walk`
/// - witness: `codec::tests::supported_tables_round_trip_and_reject_forged_support`
#[spec(ensures: |ret| (!matches!(former.sort(), Sort::ValueType | Sort::CompType) || ret.0.is_empty())
    && former.children().iter().all(|(child, _)| nodes.get(usize::from(child)).is_none_or(|child|
        child.type_reads.is_subset(&ret.1)
        && child.value_reads.is_subset(if matches!(former.sort(), Sort::ValueType | Sort::CompType)
            { &ret.1 } else { &ret.0 }))))]
pub fn references_of(
    former: &ContentNode<()>,
    nodes: &[SupportedNode],
) -> (BTreeSet<Reference>, BTreeSet<Reference>, Opacity)
{
    let mut value_reads = BTreeSet::new();
    let mut type_reads = BTreeSet::new();
    let mut opacity = if matches!(*former, ContentNode::Unresolved(_)) {
        Opacity::Opaque
    }
    else {
        Opacity::Transparent
    };
    let in_type = matches!(former.sort(), Sort::ValueType | Sort::CompType);
    if let Maybe::Present(reference) = former.reference() {
        let target = if in_type {
            &mut type_reads
        }
        else {
            &mut value_reads
        };
        target.insert(reference.clone());
    }
    for (child, _) in former.children().iter() {
        if let Some(child) = nodes.get(usize::from(child)) {
            type_reads.extend(child.type_reads.iter().cloned());
            let target = if in_type {
                &mut type_reads
            }
            else {
                &mut value_reads
            };
            target.extend(child.value_reads.iter().cloned());
            if child.opacity == Opacity::Opaque {
                opacity = Opacity::Opaque;
            }
        }
    }
    (value_reads, type_reads, opacity)
}

/// A post-order action over an arena-derived table.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// Schedule children before assembly.
    Enter(NodeIndex),
    /// Assemble after every child has its compact placement.
    Exit(NodeIndex),
}

/// A compact table and the placement of each source node in it.
pub struct Factored
{
    /// Hash-consed nodes, children before parents.
    pub nodes: Vec<SupportedNode>,
    /// One placement per input table entry.
    pub placements: Vec<Placed>,
}

/// Factor an acyclic arena-derived table into minimal scopes and covers.
///
/// # Specification
/// - requires: `raw` is acyclic and every child index resolves, as arena
///   construction guarantees; unresolved arena ids are explicit leaf formers.
/// - ensures: each raw node has an exact placement; equal compact formers and
///   covers share one entry, independently of unused ambient indices.
/// - provides: an iterative, stack-independent content encoding.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — reference support agrees with an independent arena walk;
///   L3 — relocation, wiring near-misses and de Bruijn expansion separate false
///   sharing from failure to share; dangling leaves remain opaque.
/// - witness: `tests::incremental::carried_footprint_matches_reference_walk`
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
#[spec(captures: sorts = raw.iter().map(ContentNode::sort).collect::<Vec<_>>(),
    ensures: |ret| ret.placements.len() == sorts.len()
        && ret.placements.iter().zip(sorts.iter().copied()).all(|(placed, sort)|
            ret.nodes.get(usize::from(placed.node)).is_some_and(|node|
                node.scope == placed.thinning.scope() && node.sort() == sort)))]
pub fn factor(raw: Vec<ContentNode>) -> Factored
{
    let mut raw: Vec<Option<ContentNode>> = raw.into_iter().map(Some).collect();
    let mut nodes: Vec<SupportedNode> = Vec::with_capacity(raw.len());
    let mut placements = alloc::vec![Placed::default(); raw.len()];
    let mut done = alloc::vec![false; raw.len()];
    let mut hashes: BTreeMap<u64, Vec<NodeIndex>> = BTreeMap::new();
    let mut work = Vec::new();
    for root in 0 .. raw.len() {
        work.push(Visit::Enter(NodeIndex::from(root)));
        while let Some(visit) = work.pop() {
            let index = match visit {
                | Visit::Enter(index) | Visit::Exit(index) => index,
            };
            if done.get(usize::from(index)).copied().unwrap_or(false) {
                continue;
            }
            let Some(node) = raw.get(usize::from(index)).and_then(Option::as_ref)
            else {
                continue;
            };
            if matches!(visit, Visit::Enter(_)) {
                work.push(Visit::Exit(index));
                let start = work.len();
                work.extend(node.children().iter().map(|(child, _)| Visit::Enter(child)));
                if let Some(children) = work.get_mut(start ..) {
                    children.reverse();
                }
                continue;
            }
            let Some(node) = raw.get_mut(usize::from(index)).and_then(Option::take)
            else {
                continue;
            };
            let mut thinning = Thinning::default();
            if let ContentNode::Variable { zone, index } = node {
                match zone {
                    | Zone::Intuitionistic => thinning.intuitionistic.push(index),
                    | Zone::Linear => thinning.linear.push(index),
                }
            }
            for (slot, (child, _)) in node.children().iter().enumerate() {
                if let Some(child) = placements.get(usize::from(child)) {
                    join(
                        &mut thinning,
                        &child.thinning,
                        binding(&node, ChildSlot(slot)),
                    );
                }
            }
            let mut cover = Vec::with_capacity(node.children().iter().count());
            for (slot, (child, _)) in node.children().iter().enumerate() {
                if let Some(child) = placements.get(usize::from(child)) {
                    cover.push(embedding(
                        &child.thinning,
                        &thinning,
                        binding(&node, ChildSlot(slot)),
                    ));
                }
            }
            let former = map_node(
                node,
                &mut |child| {
                    placements
                        .get(usize::from(child))
                        .map_or(child, |placed| placed.node)
                },
                &mut |_, _| (),
            );
            let supported = assemble(former, cover, thinning.scope(), &nodes);
            let mut hasher = std::hash::DefaultHasher::new();
            supported.hash(&mut hasher);
            let bucket = hashes.entry(hasher.finish()).or_default();
            let canonical = bucket
                .iter()
                .copied()
                .find(|index| nodes.get(usize::from(*index)) == Some(&supported));
            let canonical = canonical.unwrap_or_else(|| {
                let index = NodeIndex::from(nodes.len());
                nodes.push(supported);
                bucket.push(index);
                index
            });
            if let Some(placed) = placements.get_mut(usize::from(index)) {
                *placed = Placed {
                    node: canonical,
                    thinning,
                };
            }
            if let Some(done) = done.get_mut(usize::from(index)) {
                *done = true;
            }
        }
    }
    Factored { nodes, placements }
}

/// A compact table reordered by breadth-first discovery, with its index map.
pub struct Numbered
{
    /// The reordered entries.
    pub nodes: Vec<SupportedNode>,
    /// Old index to new index, for reached entries.
    pub numbers: BTreeMap<NodeIndex, NodeIndex>,
}

/// Ownership available while a compact table is renumbered.
pub enum TableSource<'nodes>
{
    /// Signature extraction borrows its item's table and copies only reached
    /// nodes.
    Borrowed(&'nodes [SupportedNode]),
    /// Encoding moves nodes out once; empty slots have already been numbered.
    Owned(Vec<Option<SupportedNode>>),
}

impl From<Vec<SupportedNode>> for TableSource<'_>
{
    /// Transfer node ownership into a consumable numbering source.
    ///
    /// # Specification
    /// trivial.
    fn from(nodes: Vec<SupportedNode>) -> Self
    {
        Self::Owned(nodes.into_iter().map(Some).collect())
    }
}

impl TableSource<'_>
{
    /// Obtain a reached node, moving owned payloads and copying borrowed ones.
    ///
    /// # Specification
    /// - requires: an owned node is requested at most once.
    /// - ensures: the node at the index; absent only for an out-of-range or
    ///   already consumed index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signature extraction and whole-item numbering agree
    ///   despite taking different ownership paths.
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(captures: entry = match *self {
        TableSource::Borrowed(nodes) => nodes.get(usize::from(index)).cloned(),
        TableSource::Owned(ref nodes) => nodes.get(usize::from(index)).and_then(Option::as_ref).cloned(),
    }, ensures: |ret| match ret {
        Maybe::Present(ref node) => entry.as_ref() == Some(node),
        Maybe::Absent(_) => entry.is_none(),
    })]
    fn take(
        &mut self,
        index: NodeIndex,
    ) -> Maybe<SupportedNode, crate::content::site::Absent>
    {
        let node = match *self {
            | Self::Borrowed(nodes) => nodes.get(usize::from(index)).cloned(),
            | Self::Owned(ref mut nodes) => {
                nodes.get_mut(usize::from(index)).and_then(Option::take)
            },
        };
        match node {
            | Some(node) => Maybe::Present(node),
            | None => Maybe::Absent(crate::content::site::Absent::Unreached),
        }
    }
}

/// Renumber the reachable compact nodes from `roots`, left to right.
///
/// # Specification
/// - requires: every root and child index resolves in `nodes`.
/// - ensures: every reachable entry appears once in breadth-first order, with
///   covers and supports unchanged and every child index translated.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a signature interleaved with a body equals its separately
///   encoded type after renumbering, including its covers and root support.
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
#[spec(ensures: |ret| ret.numbers.len() == ret.nodes.len()
    && ret.numbers.values().all(|index| usize::from(*index) < ret.nodes.len())
    && roots.iter().all(|root| ret.numbers.contains_key(root)))]
pub fn number(
    mut source: TableSource<'_>,
    roots: &[NodeIndex],
) -> Numbered
{
    let mut numbers = BTreeMap::new();
    let mut queue = VecDeque::new();
    for &root in roots {
        let next = NodeIndex::from(numbers.len());
        if let alloc::collections::btree_map::Entry::Vacant(entry) = numbers.entry(root) {
            entry.insert(next);
            queue.push_back(root);
        }
    }
    let capacity = match source {
        | TableSource::Borrowed(nodes) => nodes.len(),
        | TableSource::Owned(ref nodes) => nodes.len(),
    };
    let mut table = Vec::with_capacity(capacity);
    while let Some(old) = queue.pop_front() {
        let Maybe::Present(node) = source.take(old)
        else {
            continue;
        };
        let former = map_node(
            node.former,
            &mut |child| {
                let next = NodeIndex::from(numbers.len());
                *numbers.entry(child).or_insert_with(|| {
                    queue.push_back(child);
                    next
                })
            },
            &mut |_, ()| (),
        );
        table.push(SupportedNode { former, ..node });
    }
    Numbered {
        nodes: table,
        numbers,
    }
}

/// Expand a compact root into its de Bruijn view, retaining DAG sharing by
/// both node identity and placement.
///
/// # Specification
/// - requires: the table and root thinning are validated co-de Bruijn content.
/// - ensures: every variable recovers its ambient index; separate placements of
///   one compact node expand separately when their indices differ.
/// - fails: `expansion::Absent::IndexOverflow` if a binder shifts an ambient
///   index beyond u32; no truncated or saturated index escapes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the same pair under two unused-binder interleavings and
///   every binding former reconstruct their original indices exactly.
/// - witness: `content::tests::unused_binder_interleavings_share_one_node`
/// - witness: `content::tests::covers_preserve_every_binding_former`
/// - witness: `content::tests::debruijn_projection_reports_index_overflow`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref table) => table.iter().all(|node| node.children().iter().all(|(child, sort)|
        table.get(usize::from(child)).is_some_and(|node| node.sort() == sort))),
    Maybe::Absent(expansion::Absent::IndexOverflow) => true,
})]
pub fn expand(
    nodes: &[SupportedNode],
    root: Placed,
) -> Maybe<Vec<ContentNode>, expansion::Absent>
{
    let mut numbered = BTreeMap::from([(root.clone(), NodeIndex::from(0_usize))]);
    let mut queue = VecDeque::from([root]);
    let mut output = Vec::new();
    while let Some(placed) = queue.pop_front() {
        let Some(node) = nodes.get(usize::from(placed.node))
        else {
            continue;
        };
        let mut slot = 0_usize;
        let mut overflow = false;
        let former = map_node(
            node.former.clone(),
            &mut |child| {
                let under = binding(&node.former, ChildSlot(slot));
                let selection = node.cover.get(slot);
                slot = slot.saturating_add(1);
                let mut thinning = Thinning::default();
                if let Some(selection) = selection {
                    for (zone, target) in [
                        (Zone::Intuitionistic, &mut thinning.intuitionistic),
                        (Zone::Linear, &mut thinning.linear),
                    ] {
                        let shift =
                            u32::from(zone == Zone::Intuitionistic && under == Binding::Bound);
                        for index in selection.indices(zone) {
                            let index = u32::from(*index);
                            if index < shift {
                                target.push(DeBruijnIndex::from(0));
                            }
                            else if let Some(ambient) = placed.thinning.indices(zone).get(
                                usize::try_from(index.saturating_sub(shift)).unwrap_or(usize::MAX),
                            ) {
                                let Some(index) = u32::from(*ambient).checked_add(shift)
                                else {
                                    overflow = true;
                                    return child;
                                };
                                target.push(DeBruijnIndex::from(index));
                            }
                        }
                    }
                }
                let child = Placed {
                    node: child,
                    thinning,
                };
                let next = NodeIndex::from(numbered.len());
                *numbered.entry(child.clone()).or_insert_with(|| {
                    queue.push_back(child);
                    next
                })
            },
            &mut |zone, ()| {
                placed
                    .thinning
                    .indices(zone)
                    .first()
                    .copied()
                    .unwrap_or_else(|| DeBruijnIndex::from(0))
            },
        );
        if overflow {
            return Maybe::Absent(expansion::Absent::IndexOverflow);
        }
        output.push(former);
    }
    Maybe::Present(output)
}
