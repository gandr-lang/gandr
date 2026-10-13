//! Closed effect rows and inline operation signatures.
//!
//! A signature names an interface whose payload and reply types belong to the
//! same core arena as its uses. Signatures are shared, not recursively owned.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::ValueTypeId;

pub mod capability;

pub mod host;

/// The name of an effect interface.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EffectName(Arc<str>);

impl From<&str> for EffectName
{
    /// Copy an interface name into shared storage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(Arc::from(name))
    }
}

impl AsRef<str> for EffectName
{
    /// Borrow the interface's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// The name of an operation within one interface.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OperationName(Arc<str>);

impl From<&str> for OperationName
{
    /// Copy an operation name into shared storage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(Arc::from(name))
    }
}

impl AsRef<str> for OperationName
{
    /// Borrow the operation's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// An operation's payload and reply types.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EffectOp<Id = ValueTypeId>
{
    /// The name resolved by perform and handler clauses.
    pub name: OperationName,
    /// The value type accepted by perform.
    pub payload: Id,
    /// The value type supplied by a resumption.
    pub reply: Id,
}

/// The immutable data of one inline signature.
#[derive(Debug, Eq, Hash, PartialEq)]
struct Signature<Id>
{
    /// The interface name used as a row key.
    name: EffectName,
    /// Operations in canonical name order.
    operations: BTreeMap<OperationName, EffectOp<Id>>,
}

/// An inline-carried effect interface, shared across occurrences and rows.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EffectSig<Id = ValueTypeId>(Arc<Signature<Id>>);

/// Why a signature or row cannot denote a single interface per name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EffectConflict
{
    /// Two operations in one interface have the same name.
    DuplicateOperation(OperationName),
    /// Two distinct definitions claim one interface name.
    Signature(EffectName),
}

impl core::fmt::Display for EffectConflict
{
    /// Identify the conflicting interface or operation.
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
            | Self::DuplicateOperation(ref name) => {
                write!(f, "duplicate operation {}", name.as_ref())
            },
            | Self::Signature(ref name) => write!(f, "conflicting effect {}", name.as_ref()),
        }
    }
}

impl core::error::Error for EffectConflict
{
}

/// A requested operation does not belong to the interface.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnknownOperation;

impl<Id: Copy + Eq + 'static> EffectSig<Id>
{
    /// Relocate payload and reply handles in canonical operation order.
    ///
    /// # Specification
    /// - ensures: names and operation coverage are unchanged; payload precedes
    ///   reply.
    /// - fails: propagates the first mapper error without changing this
    ///   signature.
    ///
    /// # Errors
    /// Returns the mapper's first error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-operation interface records the mapper's visits
    ///   in name order, payload before reply; a failing mapper's error comes
    ///   back unchanged.
    /// - witness: `effect::tests::relocation_keeps_names_and_refuses_duplicate_interfaces`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body maps every operation once; the check compares each name once"
        )
    )]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|mapped| mapped.name() == self.name() && mapped.operations().map(|op| &op.name).eq(self.operations().map(|op| &op.name))))]
    pub fn try_relocate<To, E, Map>(
        &self,
        mut map: Map,
    ) -> Result<EffectSig<To>, E>
    where
        To: Copy + Eq + 'static,
        Map: FnMut(Id) -> Result<To, E>,
    {
        let mut operations = BTreeMap::new();
        for operation in self.operations() {
            let payload = map(operation.payload)?;
            let reply = map(operation.reply)?;
            operations.insert(operation.name.clone(), EffectOp {
                name: operation.name.clone(),
                payload,
                reply,
            });
        }
        Ok(EffectSig(Arc::new(Signature {
            name: self.name().clone(),
            operations,
        })))
    }

    /// Construct a signature with exactly one definition of each operation.
    ///
    /// # Specification
    /// - ensures: operation lookup is independent of input order.
    /// - fails: duplicate operation names are refused.
    ///
    /// # Errors
    /// Returns `DuplicateOperation` for the first repeated name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reordered and missing operations distinguish lookup
    ///   from positional access; a duplicate distinguishes a map from
    ///   overwriting.
    /// - witness: `effect::tests::signature_resolves_operations_by_name`
    #[inline]
    #[spec(captures: expected = name.clone(), ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|sig| sig.name() == &expected))]
    pub fn new<Operations>(
        name: EffectName,
        operations: Operations,
    ) -> Result<Self, EffectConflict>
    where
        Operations: IntoIterator<Item = EffectOp<Id>>,
    {
        let mut canonical = BTreeMap::new();
        for operation in operations {
            match canonical.entry(operation.name.clone()) {
                | alloc::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(operation);
                },
                | alloc::collections::btree_map::Entry::Occupied(_) => {
                    return Err(EffectConflict::DuplicateOperation(operation.name));
                },
            }
        }
        Ok(Self(Arc::new(Signature {
            name,
            operations: canonical,
        })))
    }

    /// Borrow the interface name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn name(&self) -> &EffectName
    {
        &self.0.name
    }

    /// Enumerate operations in name order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn operations(&self) -> impl ExactSizeIterator<Item = &EffectOp<Id>>
    {
        self.0.operations.values()
    }

    /// Resolve an operation by name.
    ///
    /// # Specification
    /// - provides: `UnknownOperation` means the name is outside this interface.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct payload and reply types distinguish the two
    ///   operations, while an absent name distinguishes a fabricated reply.
    /// - witness: `effect::tests::signature_resolves_operations_by_name`
    #[inline]
    #[spec(ensures: |ret| match ret { Maybe::Present(op) => &op.name == name, Maybe::Absent(_) => !self.0.operations.contains_key(name) })]
    pub fn operation(
        &self,
        name: &OperationName,
    ) -> Maybe<&EffectOp<Id>, UnknownOperation>
    {
        match self.0.operations.get(name) {
            | Some(operation) => Maybe::Present(operation),
            | None => Maybe::Absent(UnknownOperation),
        }
    }

    /// Payload and reply edges in canonical operation order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn types(&self) -> impl DoubleEndedIterator<Item = Id> + Clone + '_
    {
        self.0
            .operations
            .values()
            .flat_map(|operation| [operation.payload, operation.reply])
    }

    /// Rewrite interface type edges without copying an unchanged interface.
    ///
    /// # Specification
    /// - ensures: preserves the interface and operation names.
    /// - fails: propagates the mapper error without mutating this signature.
    ///
    /// # Errors
    /// Returns the first error produced by the mapper.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — opposite payload and reply types distinguish edge
    ///   order.
    /// - witness: `effect::tests::operation_types_survive_substitution_and_import`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|signature| signature.name() == self.name() && signature.0.operations.len() == self.0.operations.len()) || ret.is_err())]
    #[inline]
    pub fn try_map_types<E, Map>(
        &self,
        order: TypeOrder,
        mut map: Map,
    ) -> Result<Self, E>
    where
        Map: FnMut(Id) -> Result<Id, E>,
    {
        Ok(match self.remap_operations(order, &mut map)? {
            | Some(operations) => Self(Arc::new(Signature {
                name: self.name().clone(),
                operations,
            })),
            | None => self.clone(),
        })
    }

    /// Build a replacement operation map only when a type edge changes.
    ///
    /// # Specification
    /// - ensures: an absent replacement means every mapped edge was unchanged.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — substitution beneath binders distinguishes payload
    ///   and reply edges.
    /// - witness: `effect::tests::operation_types_survive_substitution_and_import`
    #[spec(ensures: |ret| match ret { Ok(Some(ref operations)) => operations.len() == self.0.operations.len(), _ => true })]
    fn remap_operations<E>(
        &self,
        order: TypeOrder,
        map: &mut impl FnMut(Id) -> Result<Id, E>,
    ) -> Result<Option<BTreeMap<OperationName, EffectOp<Id>>>, E>
    {
        let mut rewritten = None;
        let mut entries = self.0.operations.iter();
        while let Some((name, operation)) = match order {
            | TypeOrder::Forward => entries.next(),
            | TypeOrder::Reverse => entries.next_back(),
        } {
            let (payload, reply) = match order {
                | TypeOrder::Forward => (map(operation.payload)?, map(operation.reply)?),
                | TypeOrder::Reverse => {
                    let reply = map(operation.reply)?;
                    (map(operation.payload)?, reply)
                },
            };
            if (payload, reply) != (operation.payload, operation.reply) {
                rewritten
                    .get_or_insert_with(|| self.0.operations.clone())
                    .insert(name.clone(), EffectOp {
                        name: name.clone(),
                        payload,
                        reply,
                    });
            }
        }
        Ok(rewritten)
    }
}

impl EffectSig
{
    /// Compare operation names and their type syntax in the owning arena.
    ///
    /// # Specification
    /// - ensures: included interfaces have identical names, operation coverage
    ///   and structurally equal payload and reply types.
    /// - fails: a missing operation, changed type or unreadable type is
    ///   excluded.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal types allocated twice remain the same
    ///   interface.
    /// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
    #[spec(ensures: |ret| ret != RowInclusion::Included || (self.name() == other.name() && self.0.operations.len() == other.0.operations.len()))]
    #[inline]
    #[must_use]
    pub fn inclusion(
        &self,
        other: &Self,
        arena: &crate::CoreArena,
    ) -> RowInclusion
    {
        if self.name() != other.name() || self.operations().len() != other.operations().len() {
            return RowInclusion::Excluded;
        }
        for (left, right) in self.operations().zip(other.operations()) {
            if left.name != right.name
                || crate::syntax::equal_type_syntax(arena, left.payload, right.payload)
                    != crate::CertificateEquality::Equal
                || crate::syntax::equal_type_syntax(arena, left.reply, right.reply)
                    != crate::CertificateEquality::Equal
            {
                return RowInclusion::Excluded;
            }
        }
        RowInclusion::Included
    }
}

/// A closed finite set of interfaces in canonical name order.
///
/// Empty rows allocate nothing; cloning a nonempty row shares its immutable
/// map.
#[repr(transparent)]
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct EffectRow<Id = ValueTypeId>(Option<Arc<BTreeMap<EffectName, EffectSig<Id>>>>);

impl<Id: Copy + Eq + 'static> core::fmt::Debug for EffectRow<Id>
{
    /// Render the canonical interface names without arena-local type
    /// identities.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str("⟨")?;
        for (index, signature) in self.signatures().enumerate() {
            if index != 0 {
                f.write_str(", ")?;
            }
            f.write_str(signature.name().as_ref())?;
        }
        f.write_str("⟩")
    }
}

impl<Id> Default for EffectRow<Id>
{
    /// Construct the allocation-free pure row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self(None)
    }
}

/// Whether a computation's row permits an operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EffectPresence
{
    /// The row contains the interface.
    Present,
    /// The row does not contain the interface.
    Absent,
}

/// Whether a row performs no effects, the pure before the effectful.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Purity
{
    /// No effect interface occurs.
    Pure,
    /// At least one interface occurs.
    Effectful,
}

/// Inclusion between rows with the same definitions at shared names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RowInclusion
{
    /// Every interface is permitted by the receiving row.
    Included,
    /// An interface is absent or differently defined.
    Excluded,
}

impl<Id: Copy + Eq + 'static> EffectRow<Id>
{
    /// The pure returner's empty row.
    pub const EMPTY: Self = Self(None);

    /// A shared empty map for this handle family.
    const EMPTY_ENTRIES: &'static BTreeMap<EffectName, EffectSig<Id>> = &BTreeMap::new();

    /// Borrow the canonical entries, including the allocation-free empty case.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entries(&self) -> &BTreeMap<EffectName, EffectSig<Id>>
    {
        self.0.as_deref().unwrap_or(Self::EMPTY_ENTRIES)
    }

    /// The row permitting exactly one interface.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn singleton(signature: EffectSig<Id>) -> Self
    {
        Self(Some(Arc::new(BTreeMap::from([(
            signature.name().clone(),
            signature,
        )]))))
    }

    /// Classify the empty row as pure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn purity(&self) -> Purity
    {
        if self.0.is_none() {
            Purity::Pure
        }
        else {
            Purity::Effectful
        }
    }
}

impl EffectRow
{
    /// Join the demands of two computations.
    ///
    /// # Specification
    /// - ensures: each input is included in a successful union.
    /// - fails: distinct definitions of one name are refused.
    ///
    /// # Errors
    /// Returns `Signature` for the first conflicting shared name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — disjoint, identical and conflicting inputs
    ///   distinguish union from intersection, replacement and duplicate
    ///   accumulation.
    /// - witness: `effect::tests::union_is_a_canonical_set_and_without_subtracts`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the other row's interfaces and copies this row's map on growth; the check compares each interface of both rows with the union once"
        )
    )]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|row| self.is_subset(row, arena) == RowInclusion::Included && other.is_subset(row, arena) == RowInclusion::Included))]
    pub fn union(
        &self,
        other: &Self,
        arena: &crate::CoreArena,
    ) -> Result<Self, EffectConflict>
    {
        if self.purity() == Purity::Pure {
            return Ok(other.clone());
        }
        let mut expanded = None;
        for (name, signature) in other.entries() {
            match self.entries().get(name) {
                | Some(existing) => {
                    if existing.inclusion(signature, arena) == RowInclusion::Excluded {
                        return Err(EffectConflict::Signature(name.clone()));
                    }
                },
                | None => {
                    expanded
                        .get_or_insert_with(|| self.entries().clone())
                        .insert(name.clone(), signature.clone());
                },
            }
        }
        Ok(match expanded {
            | Some(entries) => Self(Some(Arc::new(entries))),
            | None => self.clone(),
        })
    }
}

impl<Id: Copy + Eq + 'static> EffectRow<Id>
{
    /// Remove the interface discharged by a handler.
    ///
    /// # Specification
    /// - ensures: the named interface is absent; all others are preserved.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — subtracting present and absent names distinguishes
    ///   selective removal from clearing and identity.
    /// - witness: `effect::tests::union_is_a_canonical_set_and_without_subtracts`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.contains(name) == EffectPresence::Absent && ret.entries().len() == self.entries().len().saturating_sub(usize::from(self.entries().contains_key(name))))]
    pub fn without(
        &self,
        name: &EffectName,
    ) -> Self
    {
        if !self.entries().contains_key(name) {
            return self.clone();
        }
        if self.entries().len() == 1 {
            return Self::EMPTY;
        }
        let mut signatures = self.entries().clone();
        signatures.remove(name);
        Self(Some(Arc::new(signatures)))
    }

    /// Decide name membership.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn contains(
        &self,
        name: &EffectName,
    ) -> EffectPresence
    {
        if self.entries().contains_key(name) {
            EffectPresence::Present
        }
        else {
            EffectPresence::Absent
        }
    }
}

impl EffectRow
{
    /// Decide whether every demand is allowed by `other`.
    ///
    /// # Specification
    /// - ensures: inclusion requires equal definitions at every demanded name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — proper subsets and conflicting definitions
    ///   distinguish permission inclusion from name equality alone.
    /// - witness: `effect::tests::subset_is_a_preorder_with_union_as_join`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body compares every demanded interface once; the check compares each once more"
        )
    )]
    #[spec(ensures: |ret| (ret == RowInclusion::Included) == self.entries().iter().all(|(name, sig)| other.entries().get(name).is_some_and(|other| sig.inclusion(other, arena) == RowInclusion::Included)))]
    pub fn is_subset(
        &self,
        other: &Self,
        arena: &crate::CoreArena,
    ) -> RowInclusion
    {
        if self.entries().iter().all(|(name, signature)| {
            other
                .entries()
                .get(name)
                .is_some_and(|other| signature.inclusion(other, arena) == RowInclusion::Included)
        }) {
            RowInclusion::Included
        }
        else {
            RowInclusion::Excluded
        }
    }
}

/// Traversal order when a type mapper reads or fills an ordered work stack.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeOrder
{
    /// Interface name, operation name, then payload before reply.
    Forward,
    /// The reverse order, for consuming postorder results.
    Reverse,
}

impl<Id: Copy + Eq + 'static> EffectRow<Id>
{
    /// Enumerate the permitted interfaces in name order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn signatures(&self) -> impl ExactSizeIterator<Item = &EffectSig<Id>>
    {
        self.entries().values()
    }

    /// Operation payload and reply types, in canonical interface and operation
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn types(&self) -> impl DoubleEndedIterator<Item = Id> + Clone + '_
    {
        self.entries().values().flat_map(|signature| {
            signature
                .0
                .operations
                .values()
                .flat_map(|operation| [operation.payload, operation.reply])
        })
    }

    /// Remap type edges in the requested canonical order, sharing unchanged
    /// maps.
    ///
    /// # Specification
    /// - ensures: preserves names and operation coverage, sharing unchanged
    ///   maps.
    /// - fails: propagates a mapper error without changing this row.
    ///
    /// # Errors
    /// Returns the first error produced by the type mapper.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — opposite operation directions distinguish reversed
    ///   payload and reply edges during substitution and cross-arena import.
    /// - witness: `effect::tests::operation_types_survive_substitution_and_import`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|row| row.entries().len() == self.entries().len()))]
    #[inline]
    pub fn try_map_types<E, Map>(
        &self,
        order: TypeOrder,
        mut map: Map,
    ) -> Result<Self, E>
    where
        Map: FnMut(Id) -> Result<Id, E>,
    {
        let mut rewritten = None;
        let mut signatures = self.entries().iter();
        while let Some((name, signature)) = match order {
            | TypeOrder::Forward => signatures.next(),
            | TypeOrder::Reverse => signatures.next_back(),
        } {
            if let Some(operations) = signature.remap_operations(order, &mut map)? {
                rewritten
                    .get_or_insert_with(|| self.entries().clone())
                    .insert(
                        name.clone(),
                        EffectSig(Arc::new(Signature {
                            name: name.clone(),
                            operations,
                        })),
                    );
            }
        }
        Ok(match rewritten {
            | Some(entries) => Self(Some(Arc::new(entries))),
            | None => self.clone(),
        })
    }

    /// Relocate type edges to another handle family in canonical forward order.
    ///
    /// # Specification
    /// - ensures: every operation retains its name and the images of its
    ///   payload and reply; an empty row remains allocation-free.
    /// - fails: propagates the first mapper error.
    ///
    /// # Errors
    /// Returns the mapper's error without changing this row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — relocating a row keeps its interfaces and their
    ///   images, and an empty row stays the allocation-free empty row.
    /// - witness: `effect::tests::relocation_keeps_names_and_refuses_duplicate_interfaces`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|row| row.entries().len() == self.entries().len()) || ret.is_err())]
    pub fn try_relocate<To, E, Map>(
        &self,
        mut map: Map,
    ) -> Result<EffectRow<To>, E>
    where
        To: Copy + Eq + 'static,
        Map: FnMut(Id) -> Result<To, E>,
    {
        let mut entries = BTreeMap::new();
        for signature in self.signatures() {
            entries.insert(signature.name().clone(), signature.try_relocate(&mut map)?);
        }
        Ok(if entries.is_empty() {
            EffectRow::EMPTY
        }
        else {
            EffectRow(Some(Arc::new(entries)))
        })
    }

    /// Construct a canonical row while refusing duplicate interface names.
    ///
    /// # Specification
    /// - fails: a repeated interface name is refused, never overwritten.
    ///
    /// # Errors
    /// Returns `Signature` for the first duplicate name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two interfaces of one name are refused by that name,
    ///   distinct names build the same row as their union, and none builds the
    ///   empty row.
    /// - witness: `effect::tests::relocation_keeps_names_and_refuses_duplicate_interfaces`
    #[inline]
    #[spec(ensures: |ret| !matches!(ret, Err(EffectConflict::DuplicateOperation(_))))]
    pub fn from_signatures<Signatures>(signatures: Signatures) -> Result<Self, EffectConflict>
    where
        Signatures: IntoIterator<Item = EffectSig<Id>>,
    {
        let mut entries = BTreeMap::new();
        for signature in signatures {
            match entries.entry(signature.name().clone()) {
                | alloc::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(signature);
                },
                | alloc::collections::btree_map::Entry::Occupied(entry) => {
                    return Err(EffectConflict::Signature(entry.key().clone()));
                },
            }
        }
        Ok(if entries.is_empty() {
            Self::EMPTY
        }
        else {
            Self(Some(Arc::new(entries)))
        })
    }
}

#[cfg(test)]
mod tests
{
    use super::*;

    /// Build one nullary operation for the row laws.
    ///
    /// # Specification
    /// trivial.
    fn signature(
        name: EffectName,
        payload: ValueTypeId,
    ) -> EffectSig
    {
        EffectSig::new(name, alloc::vec![EffectOp {
            name: OperationName::from("run"),
            payload,
            reply: payload
        }])
        .unwrap()
    }

    #[test]
    fn empty_is_the_bottom()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let row = EffectRow::singleton(signature(EffectName::from("State"), unit));
        assert_eq!(Purity::Pure, EffectRow::<ValueTypeId>::EMPTY.purity());
        assert_eq!(Purity::Effectful, row.purity());
        assert_eq!(
            RowInclusion::Included,
            EffectRow::EMPTY.is_subset(&row, &arena)
        );
        assert_eq!(
            RowInclusion::Included,
            EffectRow::EMPTY.is_subset(&EffectRow::EMPTY, &arena)
        );
    }

    #[test]
    fn subset_is_a_preorder_with_union_as_join()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let state = EffectRow::singleton(signature(EffectName::from("State"), unit));
        let io = EffectRow::singleton(signature(EffectName::from("IO"), unit));
        let joined = state.union(&io, &arena).unwrap();
        assert_eq!(RowInclusion::Included, state.is_subset(&state, &arena));
        assert_eq!(RowInclusion::Included, state.is_subset(&joined, &arena));
        assert_eq!(RowInclusion::Included, io.is_subset(&joined, &arena));
        assert_eq!(RowInclusion::Excluded, joined.is_subset(&state, &arena));
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        let conflicting = EffectRow::singleton(signature(EffectName::from("State"), integer));
        assert_eq!(
            RowInclusion::Excluded,
            state.is_subset(&conflicting, &arena)
        );
        assert_eq!(
            Err(EffectConflict::Signature(EffectName::from("State"))),
            state.union(&conflicting, &arena)
        );
    }

    #[test]
    fn union_is_a_canonical_set_and_without_subtracts()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let state = EffectRow::singleton(signature(EffectName::from("State"), unit));
        let io = EffectRow::singleton(signature(EffectName::from("IO"), unit));
        assert_eq!(state.union(&io, &arena), io.union(&state, &arena));
        assert_eq!(Ok(state.clone()), state.union(&state, &arena));
        assert_eq!(
            state,
            state
                .union(&io, &arena)
                .unwrap()
                .without(&EffectName::from("IO"))
        );
        assert_eq!(state, state.without(&EffectName::from("Absent")));
    }

    #[test]
    fn signature_resolves_operations_by_name()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        let get = EffectOp {
            name: OperationName::from("get"),
            payload: unit,
            reply: integer,
        };
        let put = EffectOp {
            name: OperationName::from("put"),
            payload: integer,
            reply: unit,
        };
        let state = EffectSig::new(EffectName::from("State"), alloc::vec![
            put.clone(),
            get.clone()
        ])
        .unwrap();
        assert_eq!(Maybe::Present(&get), state.operation(&get.name));
        assert_eq!(Maybe::Present(&put), state.operation(&put.name));
        assert_eq!(
            Maybe::Absent(UnknownOperation),
            state.operation(&OperationName::from("absent"))
        );
        assert_eq!(
            Err(EffectConflict::DuplicateOperation(get.name.clone())),
            EffectSig::new(EffectName::from("State"), alloc::vec![get.clone(), get])
        );
    }

    #[test]
    fn signature_inclusion_ignores_allocation_identity()
    {
        let mut arena = crate::CoreArena::new();
        let first_unit = arena.value_type_unit();
        let second_unit = arena.value_type_unit();
        let first_list = arena.value_type_list(first_unit);
        let second_list = arena.value_type_list(second_unit);
        let first = EffectRow::singleton(signature(EffectName::from("ListOp"), first_list));
        let second = EffectRow::singleton(signature(EffectName::from("ListOp"), second_list));
        assert_eq!(RowInclusion::Included, first.is_subset(&second, &arena));
        assert_eq!(RowInclusion::Included, second.is_subset(&first, &arena));
        assert_eq!(Ok(first.clone()), first.union(&second, &arena));
        let first_returner = arena.comp_type_returner_with_effects(first_list, first.clone());
        let second_returner = arena.comp_type_returner_with_effects(second_list, second);
        let first_thunk = arena.value_type_thunk(first_returner);
        let second_thunk = arena.value_type_thunk(second_returner);
        assert_eq!(
            RowInclusion::Included,
            signature(EffectName::from("ThunkOp"), first_thunk).inclusion(
                &signature(EffectName::from("ThunkOp"), second_thunk),
                &arena
            )
        );
        let changed = EffectRow::singleton(
            EffectSig::new(EffectName::from("ListOp"), alloc::vec![EffectOp {
                name: OperationName::from("run"),
                payload: second_list,
                reply: second_unit,
            }])
            .unwrap(),
        );
        assert_eq!(RowInclusion::Excluded, first.is_subset(&changed, &arena));
        assert_eq!(
            Err(EffectConflict::Signature(EffectName::from("ListOp"))),
            first.union(&changed, &arena)
        );
    }

    #[test]
    fn operation_types_survive_substitution_and_import()
    {
        let mut source = crate::CoreArena::new();
        let unit = source.value_type_unit();
        let variable = source.value_variable(
            crate::Zone::Intuitionistic,
            gandr_kernel_term::DeBruijnIndex::from(0_u32),
        );
        let parameter = source.value_type_element(variable, gandr_kernel_strata::Level::zero());
        let list = source.value_type_list(parameter);
        let get = OperationName::from("get");
        let put = OperationName::from("put");
        let row = EffectRow::singleton(
            EffectSig::new(EffectName::from("State"), alloc::vec![
                EffectOp {
                    name: get.clone(),
                    payload: unit,
                    reply: list
                },
                EffectOp {
                    name: put.clone(),
                    payload: list,
                    reply: unit
                },
            ])
            .unwrap(),
        );
        let open = source.comp_type_returner_with_effects(unit, row);
        let quote = source.value_quote(unit);
        let closed = crate::instantiate_comp_type(&mut source, open, quote);
        let thunk = source.value_type_thunk(closed);
        let mut target = crate::CoreArena::new();
        let _occupied = target.value_type_base(gandr_kernel_term::BaseType::String);
        let imported = crate::TypeImporter::new(&source, &mut target)
            .value_type(thunk)
            .unwrap();
        let Some(&crate::ValueType::Thunk(body)) = target.value_type(imported)
        else {
            panic!("thunk");
        };
        let Some(&crate::CompType::Returner {
            result,
            ref effects,
        }) = target.comp_type(body)
        else {
            panic!("returner");
        };
        assert_eq!(Some(&crate::ValueType::unit()), target.value_type(result));
        let signature = effects.signatures().next().unwrap();
        let Maybe::Present(get) = signature.operation(&get)
        else {
            panic!("get");
        };
        let Maybe::Present(put) = signature.operation(&put)
        else {
            panic!("put");
        };
        assert_eq!((get.payload, get.reply), (put.reply, put.payload));
        assert_eq!(
            Some(&crate::ValueType::unit()),
            target.value_type(get.payload)
        );
        let Some(&crate::ValueType::List(element)) = target.value_type(get.reply)
        else {
            panic!("list");
        };
        assert_eq!(Some(&crate::ValueType::unit()), target.value_type(element));
        let crate::CompType::Returner { ref effects, .. } = *source.comp_type(open).unwrap()
        else {
            panic!("original returner");
        };
        let original = effects.signatures().next().unwrap();
        let Maybe::Present(original_get) = original.operation(&OperationName::from("get"))
        else {
            panic!("original get");
        };
        assert_eq!(list, original_get.reply);
        assert!(matches!(
            source.value_type(parameter),
            Some(crate::ValueType::Element { .. })
        ));
    }

    #[test]
    fn relocation_keeps_names_and_refuses_duplicate_interfaces()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        let state = EffectSig::new(EffectName::from("State"), alloc::vec![
            EffectOp {
                name: OperationName::from("put"),
                payload: integer,
                reply: unit,
            },
            EffectOp {
                name: OperationName::from("get"),
                payload: unit,
                reply: integer,
            },
        ])
        .unwrap();
        let mut visited = alloc::vec::Vec::new();
        let relocated = state
            .try_relocate(|id| {
                visited.push(id);
                Ok::<_, ValueTypeId>(id)
            })
            .unwrap();
        assert_eq!(visited, [unit, integer, integer, unit]);
        assert_eq!(relocated, state);
        assert_eq!(
            state.try_relocate(|id| if id == integer { Err(id) } else { Ok(id) }),
            Err(integer)
        );
        let row = EffectRow::singleton(state.clone());
        assert_eq!(row.try_relocate(Ok::<_, ValueTypeId>), Ok(row.clone()));
        assert_eq!(
            EffectRow::<ValueTypeId>::EMPTY.try_relocate(Ok::<_, ValueTypeId>),
            Ok(EffectRow::EMPTY)
        );
        let io = signature(EffectName::from("IO"), unit);
        assert_eq!(
            EffectRow::from_signatures([state.clone(), state.clone()]),
            Err(EffectConflict::Signature(EffectName::from("State")))
        );
        assert_eq!(
            EffectRow::from_signatures([io.clone(), state]),
            row.union(&EffectRow::singleton(io), &arena)
        );
        assert_eq!(
            EffectRow::<ValueTypeId>::from_signatures([]),
            Ok(EffectRow::EMPTY)
        );
    }
}
