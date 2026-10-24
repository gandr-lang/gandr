//! The effects reading of a row, and inline operation signatures.
//!
//! A signature names an interface whose payload and reply types belong to the
//! same core arena as its uses. Signatures are shared, not recursively owned.
//! A row holds each signature under a [`Label`], the instance's name, which
//! is the interface's name until an instance is named apart; its tail is a
//! type handle like its operations' types, so every traversal of the row's
//! types carries it.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::ValueTypeId;
use crate::row::Label;
use crate::row::LabelTwice;
use crate::row::Row;
use crate::row::RowInclusion;
use crate::row::RowsApart;

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

impl From<&EffectName> for Label
{
    /// The default label of an interface's instance: its name, sharing the
    /// name's storage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &EffectName) -> Self
    {
        Self::from(Arc::clone(&name.0))
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

/// Why a signature or row cannot denote a single interface per label.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EffectConflict
{
    /// Two operations in one interface have the same name.
    DuplicateOperation(OperationName),
    /// Two distinct definitions claim one label.
    Signature(Label),
    /// Two rows open through different tails: a row has one.
    Tails,
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
            Self::DuplicateOperation(ref name) => {
                write!(f, "duplicate operation {}", name.as_ref())
            },
            Self::Signature(ref label) => write!(f, "conflicting effect {}", label.as_ref()),
            Self::Tails => f.write_str("two row variables in one row"),
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
                alloc::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(operation);
                },
                alloc::collections::btree_map::Entry::Occupied(_) => {
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
        self.0
            .operations
            .get(name)
            .map_or(Maybe::Absent(UnknownOperation), Maybe::Present)
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
        Ok(self.remap_operations(order, &mut map)?.map_or_else(
            || self.clone(),
            |operations| {
                Self(Arc::new(Signature {
                    name: self.name().clone(),
                    operations,
                }))
            },
        ))
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
            TypeOrder::Forward => entries.next(),
            TypeOrder::Reverse => entries.next_back(),
        } {
            let (payload, reply) = match order {
                TypeOrder::Forward => (map(operation.payload)?, map(operation.reply)?),
                TypeOrder::Reverse => {
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
    /// - witness: `effect::tests::a_signature_includes_another_only_at_one_name_and_one_operation_table`
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

/// The effects reading of a [`Row`]: the interfaces a returner may perform,
/// each under its label in canonical label order, closed or open through a
/// tail.
///
/// The tail is a type handle: in an arena, a
/// [`ValueType::RowTail`](crate::ValueType::RowTail) naming the row value a
/// row variable stands for. Empty rows allocate nothing; cloning a nonempty
/// row shares its immutable map.
#[repr(transparent)]
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct EffectRow<Id = ValueTypeId>(Row<Label, EffectSig<Id>, Id>);

impl<Id: Copy + Eq + 'static> core::fmt::Debug for EffectRow<Id>
{
    /// Render the canonical labels, and a tail as `| …`, without arena-local
    /// type identities.
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
        for (index, label) in self.entries().keys().enumerate() {
            if index != 0 {
                f.write_str(", ")?;
            }
            f.write_str(label.as_ref())?;
        }
        if self.tail().is_some() {
            f.write_str(if self.entries().is_empty() {
                "…"
            }
            else {
                " | …"
            })?;
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
        Self(Row::EMPTY)
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
    /// No effect interface occurs and no tail stands for more.
    Pure,
    /// An interface occurs, or a tail may stand for one.
    Effectful,
}

impl<Id: Copy + Eq + 'static> EffectRow<Id>
{
    /// The pure returner's empty row.
    pub const EMPTY: Self = Self(Row::EMPTY);

    /// Borrow the canonical entries, including the allocation-free empty case.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entries(&self) -> &BTreeMap<Label, EffectSig<Id>>
    {
        self.0.entries()
    }

    /// The closed row permitting exactly one interface, under its default
    /// label.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn singleton(signature: EffectSig<Id>) -> Self
    {
        Self(Row::singleton(Label::from(signature.name()), signature))
    }

    /// The tail the row is open through, none for a closed row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tail(&self) -> Option<Id>
    {
        self.0.tail().copied()
    }

    /// This row's interfaces, open through `tail` instead of this row's tail.
    ///
    /// # Specification
    /// - ensures: the labels and signatures are this row's and the tail is
    ///   `tail`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — opening a closed row and closing an open one
    ///   distinguish the tail's replacement from a join.
    /// - witness: `effect::tests::a_tail_rides_every_traversal_of_a_row`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.tail() == tail && ret.entries().len() == self.entries().len())]
    pub fn with_tail(
        &self,
        tail: Option<Id>,
    ) -> Self
    {
        Self(self.0.with_tail(tail))
    }

    /// Keep the interfaces whose labels `other` does not write, open through
    /// this row's tail: what a tail is solved to when a row equation forces
    /// it.
    ///
    /// # Specification
    /// - ensures: a label is kept exactly when `other` does not write it; the
    ///   tail is this row's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rows sharing some labels and none distinguish the
    ///   difference from intersection and from removal of everything.
    /// - witness: `row::tests::a_row_has_one_tail_and_inclusion_keeps_it`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.tail() == self.tail() && ret.entries().keys().all(|label| !other.entries().contains_key(label)))]
    pub fn difference(
        &self,
        other: &Self,
    ) -> Self
    {
        Self(self.0.difference(&other.0))
    }

    /// Join two rows as [`EffectRow::union`] does, a label both write agreeing
    /// only when its two signatures are one signature, type for type by id:
    /// the union read without the arena. A row and the row its tail stands
    /// for write no label in common, so a merge at mint needs no more.
    ///
    /// # Specification
    /// - ensures: a successful join holds the interfaces of both rows and the
    ///   tail of whichever is open.
    /// - fails: a label whose two signatures differ in any id, or two different
    ///   tails, are refused.
    ///
    /// # Errors
    /// Returns `Signature` for the first label whose signatures differ and
    /// `Tails` for two different tails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — apart rows, a label shared at the same ids, one
    ///   shared at equal types minted twice and rows open through two tails
    ///   distinguish identity from structural agreement and from the union.
    /// - witness: `effect::tests::a_join_by_identity_refuses_equal_types_minted_twice`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|row| row.entries().len() >= self.entries().len().max(other.entries().len()) && row.tail() == self.tail().or_else(|| other.tail())))]
    pub fn union_by_identity(
        &self,
        other: &Self,
    ) -> Result<Self, EffectConflict>
    {
        self.0
            .union(&other.0, &|ours: &EffectSig<Id>, theirs: &EffectSig<Id>| {
                if ours == theirs {
                    RowInclusion::Included
                }
                else {
                    RowInclusion::Excluded
                }
            })
            .map(Self)
            .map_err(|apart| match apart {
                RowsApart::Label(label) => EffectConflict::Signature(label),
                RowsApart::Tails(..) => EffectConflict::Tails,
            })
    }

    /// Classify a row with no interface and no tail as pure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn purity(&self) -> Purity
    {
        if self.entries().is_empty() && self.tail().is_none() {
            Purity::Pure
        }
        else {
            Purity::Effectful
        }
    }
}

impl EffectRow
{
    /// Join the demands of two computations: every label of either, and the
    /// one tail either is open through.
    ///
    /// # Specification
    /// - ensures: each input is included in a successful union.
    /// - fails: distinct definitions of one label, or two different tails, are
    ///   refused.
    ///
    /// # Errors
    /// Returns `Signature` for the first conflicting shared label and `Tails`
    /// for two different tails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — disjoint, identical and conflicting inputs, open and
    ///   closed, distinguish union from intersection, replacement, duplicate
    ///   accumulation and a dropped tail.
    /// - witness: `effect::tests::union_is_a_canonical_set_and_without_subtracts`
    /// - witness: `effect::tests::a_tail_rides_every_traversal_of_a_row`
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
        self.0
            .union(&other.0, &|ours: &EffectSig, theirs: &EffectSig| {
                ours.inclusion(theirs, arena)
            })
            .map(Self)
            .map_err(|apart| match apart {
                RowsApart::Label(label) => EffectConflict::Signature(label),
                RowsApart::Tails(..) => EffectConflict::Tails,
            })
    }
}

impl<Id: Copy + Eq + 'static> EffectRow<Id>
{
    /// Remove the instance discharged by a handler, keeping the tail.
    ///
    /// # Specification
    /// - ensures: the labelled instance is absent; all others and the tail are
    ///   preserved.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — subtracting present and absent labels distinguishes
    ///   selective removal from clearing and identity.
    /// - witness: `effect::tests::union_is_a_canonical_set_and_without_subtracts`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.contains(label) == EffectPresence::Absent && ret.tail() == self.tail() && ret.entries().len() == self.entries().len().saturating_sub(usize::from(self.entries().contains_key(label))))]
    pub fn without(
        &self,
        label: &Label,
    ) -> Self
    {
        Self(self.0.without(label))
    }

    /// Decide whether the row writes `label`; a tail's further instances are
    /// unknown and never counted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn contains(
        &self,
        label: &Label,
    ) -> EffectPresence
    {
        if self.entries().contains_key(label) {
            EffectPresence::Present
        }
        else {
            EffectPresence::Absent
        }
    }

    /// The signature written under `label`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        label: &Label,
    ) -> Option<&EffectSig<Id>>
    {
        self.0.get(label)
    }

    /// Enumerate the written labels with their signatures, in label order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn instances(&self) -> impl ExactSizeIterator<Item = (&Label, &EffectSig<Id>)>
    {
        self.entries().iter()
    }
}

impl EffectRow
{
    /// Decide whether every demand is allowed by `other`.
    ///
    /// # Specification
    /// - ensures: inclusion requires equal definitions at every demanded label,
    ///   and an open row's tail to be `other`'s.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — proper subsets, conflicting definitions and rows on
    ///   other tails distinguish permission inclusion from label equality
    ///   alone.
    /// - witness: `effect::tests::subset_is_a_preorder_with_union_as_join`
    /// - witness: `row::tests::a_row_has_one_tail_and_inclusion_keeps_it`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body compares every demanded interface once; the check compares each once more"
        )
    )]
    #[spec(ensures: |ret| (ret == RowInclusion::Included) == (self.tail().is_none_or(|tail| other.tail() == Some(tail)) && self.entries().iter().all(|(label, sig)| other.entries().get(label).is_some_and(|other| sig.inclusion(other, arena) == RowInclusion::Included))))]
    pub fn is_subset(
        &self,
        other: &Self,
        arena: &crate::CoreArena,
    ) -> RowInclusion
    {
        self.0
            .is_subset(&other.0, &|ours: &EffectSig, theirs: &EffectSig| {
                ours.inclusion(theirs, arena)
            })
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
    /// Enumerate the permitted interfaces in label order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn signatures(&self) -> impl ExactSizeIterator<Item = &EffectSig<Id>>
    {
        self.entries().values()
    }

    /// Operation payload and reply types, in canonical label and operation
    /// order, then the tail.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn types(&self) -> impl DoubleEndedIterator<Item = Id> + Clone + '_
    {
        self.entries()
            .values()
            .flat_map(|signature| {
                signature
                    .0
                    .operations
                    .values()
                    .flat_map(|operation| [operation.payload, operation.reply])
            })
            .chain(self.tail())
    }

    /// Remap type edges, the tail's included, in the requested canonical
    /// order, sharing unchanged maps.
    ///
    /// # Specification
    /// - ensures: preserves labels, names and operation coverage, sharing
    ///   unchanged maps; the tail is mapped last going forward and first in
    ///   reverse, mirroring [`Self::types`].
    /// - fails: propagates a mapper error without changing this row.
    ///
    /// # Errors
    /// Returns the first error produced by the type mapper.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — opposite operation directions distinguish reversed
    ///   payload and reply edges during substitution and cross-arena import; an
    ///   open row distinguishes the tail's position.
    /// - witness: `effect::tests::operation_types_survive_substitution_and_import`
    /// - witness: `effect::tests::a_tail_rides_every_traversal_of_a_row`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|row| row.entries().len() == self.entries().len() && row.tail().is_some() == self.tail().is_some()))]
    #[inline]
    pub fn try_map_types<E, Map>(
        &self,
        order: TypeOrder,
        mut map: Map,
    ) -> Result<Self, E>
    where
        Map: FnMut(Id) -> Result<Id, E>,
    {
        let mut tail = self.tail();
        if let (TypeOrder::Reverse, Some(written)) = (order, tail) {
            tail = Some(map(written)?);
        }
        let mut rewritten = None;
        let mut instances = self.entries().iter();
        while let Some((label, signature)) = match order {
            TypeOrder::Forward => instances.next(),
            TypeOrder::Reverse => instances.next_back(),
        } {
            if let Some(operations) = signature.remap_operations(order, &mut map)? {
                rewritten
                    .get_or_insert_with(|| self.entries().clone())
                    .insert(
                        label.clone(),
                        EffectSig(Arc::new(Signature {
                            name: signature.name().clone(),
                            operations,
                        })),
                    );
            }
        }
        if let (TypeOrder::Forward, Some(written)) = (order, tail) {
            tail = Some(map(written)?);
        }
        Ok(match rewritten {
            Some(entries) => Self(Row::from_map(entries, tail)),
            None if tail == self.tail() => self.clone(),
            None => self.with_tail(tail),
        })
    }

    /// Relocate type edges, the tail's included, to another handle family in
    /// canonical forward order.
    ///
    /// # Specification
    /// - ensures: every instance retains its label, its interface's name and
    ///   the images of its payloads and replies, and the tail its image; an
    ///   empty row remains allocation-free.
    /// - fails: propagates the first mapper error.
    ///
    /// # Errors
    /// Returns the mapper's error without changing this row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — relocating a row keeps its interfaces and their
    ///   images, an open row keeps a tail, and an empty row stays the
    ///   allocation-free empty row.
    /// - witness: `effect::tests::relocation_keeps_names_and_refuses_duplicate_interfaces`
    /// - witness: `effect::tests::a_tail_rides_every_traversal_of_a_row`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|row| row.entries().len() == self.entries().len() && row.tail().is_some() == self.tail().is_some()) || ret.is_err())]
    pub fn try_relocate<To, E, Map>(
        &self,
        mut map: Map,
    ) -> Result<EffectRow<To>, E>
    where
        To: Copy + Eq + 'static,
        Map: FnMut(Id) -> Result<To, E>,
    {
        let mut entries = BTreeMap::new();
        for (label, signature) in self.entries() {
            entries.insert(label.clone(), signature.try_relocate(&mut map)?);
        }
        let tail = self.tail().map(map).transpose()?;
        Ok(EffectRow(Row::from_map(entries, tail)))
    }

    /// Construct a closed canonical row, each interface under its default
    /// label, while refusing a label twice.
    ///
    /// # Specification
    /// - fails: a repeated label is refused, never overwritten.
    ///
    /// # Errors
    /// Returns `Signature` for the first duplicate label.
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
        Row::from_entries(
            signatures
                .into_iter()
                .map(|signature| (Label::from(signature.name()), signature)),
        )
        .map(Self)
        .map_err(|LabelTwice(label)| EffectConflict::Signature(label))
    }
}

#[cfg(test)]
mod tests;
