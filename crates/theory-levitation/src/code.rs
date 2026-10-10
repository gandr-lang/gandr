//! The first-order code universe `{1, var, ×, σ}` with its leaf decorations:
//! a graded, attributed field over a symbolic value type, and an
//! atom-abstraction.
//!
//! A [`Code`] describes one constructor's payload. The tag σ over constructors
//! lives at the description level (the constructor table of [`SignDesc`]);
//! the [`Code::sum`] former additionally represents an inline sum, so a
//! retrofitted builtin like `Boolean = 1 + 1` is one code. The fragment is
//! first-order — no function-typed field — because that is what keeps code
//! equality decidable: [`Code`] derives total structural equality and
//! hashing, the property content addressing and matching modulo rely on.
//!
//! A field's grade is the consumer's: [`Code`] is generic over it, stores it
//! as given, compares it structurally, and never interprets it.
//!
//! [`SignDesc`]: crate::SignDesc

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::AttributeEmptiness;
use crate::boundary::AttributePresence;
use crate::boundary::FirstOrderStatus;
use crate::boundary::NameRef;
use crate::boundary::RecursiveStatus;
use crate::tree::ArgumentCount;
use crate::tree::Children;
use crate::tree::Head;
use crate::tree::Tree;
use crate::tree::TreeRef;

/// A description-level name: a constructor, field, parameter, sort, port or
/// type head.
///
/// A boxed string, so [`Code`] stays a plain value with derived structural
/// equality.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Name(Box<str>);

impl From<&str> for Name
{
    /// A name spelled by the borrowed text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &str) -> Self
    {
        Self(value.into())
    }
}

impl From<NameRef<'_>> for Name
{
    /// A name spelled by the borrowed name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: NameRef<'_>) -> Self
    {
        Self(value.as_ref().into())
    }
}

impl From<&Self> for Name
{
    /// A copy of the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &Self) -> Self
    {
        value.clone()
    }
}

impl From<String> for Name
{
    /// A name spelled by the owned text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: String) -> Self
    {
        Self(value.into_boxed_str())
    }
}

impl From<Box<str>> for Name
{
    /// A name spelled by the boxed text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Box<str>) -> Self
    {
        Self(value)
    }
}

impl From<Name> for Box<str>
{
    /// The name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Name) -> Self
    {
        value.0
    }
}

impl AsRef<str> for Name
{
    /// The name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for Name
{
    /// Writes the name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

impl Name
{
    /// The name as a borrowed name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_name_ref(&self) -> NameRef<'_>
    {
        NameRef::from(&*self.0)
    }
}

/// A retrofitted primitive value type a non-recursive field can carry.
///
/// The closed set of primitive types the description leaf recognizes; any
/// other named type is a [`ValueTypeRef::ctor`]. A primitive field is an
/// opaque leaf a value decoder reads by its primitive type.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PrimTy
{
    /// The unbounded integer type `Integer`.
    Integer,
    /// The boolean type `Boolean`, whose retrofit is `1 + 1`.
    Boolean,
    /// The unit type `Unit`.
    Unit,
    /// The string type `String`.
    StringTy,
    /// The character type `Char`.
    Char,
    /// The fixed-width numeric type `u32`.
    U32,
    /// The fixed-width numeric type `u64`.
    U64,
    /// The fixed-width numeric type `i32`.
    I32,
    /// The fixed-width numeric type `i64`.
    I64,
    /// The floating type `f32`.
    F32,
    /// The floating type `f64`.
    F64,
    /// The gradual top `Unknown`, the consistency hole a field type can name.
    Unknown,
}

quenchant_shape::reason_enum! {
    /// Why a spelling names no primitive type.
    pub mod primitive_label {
        /// The reason the spelling is not a primitive.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The spelling names a declared or applied type, not one of the
            /// retrofitted primitives.
            Declared,
        }
    }
}

impl PrimTy
{
    /// Classify a primitive-type spelling.
    ///
    /// # Specification
    /// - requires: `label` is a surface type spelling.
    /// - provides: the matching primitive, or
    ///   [`primitive_label::Absent::Declared`] for a spelling that names no
    ///   primitive, which is then a named type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every primitive has an independently pinned spelling;
    ///   empty, differently cased and declared names are absent. Exact variants
    ///   and spellings separate missing arms and mutually consistent renamings.
    /// - witness: `code::tests::primitive_labels_round_trip`
    #[inline]
    #[spec(ensures: |ref prim| match *prim {
        | Maybe::Present(prim) => prim.label().as_ref() == label.as_ref(),
        | Maybe::Absent(_) => !matches!(label.as_ref(), "Integer" | "Boolean" | "Unit" | "String" | "Char" | "u32" | "u64" | "i32" | "i64" | "f32" | "f64" | "Unknown"),
    })]
    pub fn from_label(label: NameRef<'_>) -> Maybe<Self, primitive_label::Absent>
    {
        let prim = match label.as_ref() {
            | "Integer" => Self::Integer,
            | "Boolean" => Self::Boolean,
            | "Unit" => Self::Unit,
            | "String" => Self::StringTy,
            | "Char" => Self::Char,
            | "u32" => Self::U32,
            | "u64" => Self::U64,
            | "i32" => Self::I32,
            | "i64" => Self::I64,
            | "f32" => Self::F32,
            | "f64" => Self::F64,
            | "Unknown" => Self::Unknown,
            | _ => return Maybe::Absent(primitive_label::Absent::Declared),
        };
        Maybe::Present(prim)
    }

    /// The canonical spelling of this primitive.
    ///
    /// # Specification
    /// - ensures: the inverse of [`Self::from_label`] on every primitive.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all twelve variants have pinned canonical spellings,
    ///   including the case-sensitive and width-sensitive pairs; a swapped or
    ///   consistently renamed pair fails independently of the reverse lookup.
    /// - witness: `code::tests::primitive_labels_round_trip`
    #[inline]
    #[must_use]
    #[spec(ensures: |label| matches!((self, label.as_ref()),
        | (Self::Integer, "Integer")
        | (Self::Boolean, "Boolean")
        | (Self::Unit, "Unit")
        | (Self::StringTy, "String")
        | (Self::Char, "Char")
        | (Self::U32, "u32")
        | (Self::U64, "u64")
        | (Self::I32, "i32")
        | (Self::I64, "i64")
        | (Self::F32, "f32")
        | (Self::F64, "f64")
        | (Self::Unknown, "Unknown")
    ))]
    pub fn label(self) -> NameRef<'static>
    {
        NameRef::from(match self {
            | Self::Integer => "Integer",
            | Self::Boolean => "Boolean",
            | Self::Unit => "Unit",
            | Self::StringTy => "String",
            | Self::Char => "Char",
            | Self::U32 => "u32",
            | Self::U64 => "u64",
            | Self::I32 => "i32",
            | Self::I64 => "i64",
            | Self::F32 => "f32",
            | Self::F64 => "f64",
            | Self::Unknown => "Unknown",
        })
    }
}

/// One node head of a symbolic value-type reference.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum TypeHead
{
    /// A datatype parameter, by name.
    Param(Name),
    /// A retrofitted primitive.
    Prim(PrimTy),
    /// A named or applied type head over its argument count.
    Ctor(Name, ArgumentCount),
}

impl Head for TypeHead
{
    /// The head's argument count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        match *self {
            | Self::Ctor(_, arity) => arity,
            | Self::Param(_) | Self::Prim(_) => ArgumentCount::from(0_usize),
        }
    }
}

/// A symbolic reference to the value type a non-recursive field carries.
///
/// The reference stays surface-level, before type lowering, so a description
/// mirrors the declared field without committing to any core type universe;
/// mapping it to a core type is the value decoder's job, on the consumer's
/// side. A field whose type is a recursive occurrence of the datatype being
/// described is not a [`ValueTypeRef`] at all: it is [`Code::var`].
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ValueTypeRef(Tree<TypeHead>);

impl ValueTypeRef
{
    /// A datatype type parameter, by name (`a` in `Maybe(a)`).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn param<N>(name: N) -> Self
    where
        N: Into<Name>,
    {
        Self(Tree::leaf(TypeHead::Param(name.into())))
    }

    /// A retrofitted primitive value type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn prim(prim: PrimTy) -> Self
    {
        Self(Tree::leaf(TypeHead::Prim(prim)))
    }

    /// A named or applied type: a head over its argument references, left to
    /// right (empty for a bare name: `NatOp`, `Vec(a)`).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn ctor<N, A>(
        head: N,
        args: A,
    ) -> Self
    where
        N: Into<Name>,
        A: IntoIterator<Item = Self>,
    {
        let args: Vec<Tree<TypeHead>> = args.into_iter().map(|arg| arg.0).collect();
        let arity = ArgumentCount::from(args.len());
        Self(Tree::node(TypeHead::Ctor(head.into(), arity), args))
    }

    /// The reference as a borrowed node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(&self) -> ValueTypeNode<'_>
    {
        ValueTypeNode(self.0.to_ref())
    }

    /// The reference's head and arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> ValueTypeView<'_>
    {
        self.to_node().view()
    }

    /// The spelling of the reference's head: a parameter's name, a
    /// primitive's label, or a named type's head.
    ///
    /// # Specification
    /// - ensures: the parameter name for a parameter, the canonical label for a
    ///   primitive, and the head name (arguments dropped) for a named or
    ///   applied type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parameters, primitives and zero/nonzero-argument
    ///   named types have exact expected heads; returning an argument, dropping
    ///   a name or confusing a primitive with its debug spelling is separated.
    /// - witness: `wellformed::tests::the_constructor_layer_agrees_with_the_bridge_shape`
    /// - witness: `code::tests::type_heads_ignore_arguments_but_preserve_head_spelling`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref name| match *self.0.to_ref().head() {
        | TypeHead::Param(ref expected) | TypeHead::Ctor(ref expected, _) => name == expected,
        | TypeHead::Prim(prim) => name.as_ref() == prim.label().as_ref(),
    })]
    pub fn head_name(&self) -> Name
    {
        match *self.0.to_ref().head() {
            | TypeHead::Param(ref name) | TypeHead::Ctor(ref name, _) => name.clone(),
            | TypeHead::Prim(prim) => Name::from(prim.label()),
        }
    }
}

/// A borrowed node of a [`ValueTypeRef`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValueTypeNode<'code>(TreeRef<'code, TypeHead>);

impl<'code> ValueTypeNode<'code>
{
    /// The node's head and arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(self) -> ValueTypeView<'code>
    {
        match *self.0.head() {
            | TypeHead::Param(ref name) => ValueTypeView::Param(name),
            | TypeHead::Prim(prim) => ValueTypeView::Prim(prim),
            | TypeHead::Ctor(ref head, _) => ValueTypeView::Ctor {
                head,
                args: ValueTypeArgs(self.0.children()),
            },
        }
    }

    /// An owned copy of the node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_value_type_ref(self) -> ValueTypeRef
    {
        ValueTypeRef(self.0.to_tree())
    }
}

/// The head and arguments of one value-type reference node.
#[derive(Clone, Debug)]
pub enum ValueTypeView<'code>
{
    /// A datatype type parameter.
    Param(&'code Name),
    /// A retrofitted primitive.
    Prim(PrimTy),
    /// A named or applied type.
    Ctor
    {
        /// The type head (`Vec`, `NatOp`).
        head: &'code Name,
        /// The applied arguments, left to right.
        args: ValueTypeArgs<'code>,
    },
}

/// The arguments of an applied type reference, left to right.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct ValueTypeArgs<'code>(Children<'code, TypeHead>);

impl<'code> Iterator for ValueTypeArgs<'code>
{
    type Item = ValueTypeNode<'code>;

    /// The next argument.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(ValueTypeNode)
    }

    /// The exact number of remaining arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for ValueTypeArgs<'_>
{
}

/// One attribute marker in a per-symbol attribute slot (`[ctor, assoc]`).
///
/// The marker carries its name; a typed payload is erased by value decoding
/// and is not modelled here.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Attr
{
    /// The attribute marker name.
    pub name: Name,
}

impl Attr
{
    /// A bare marker attribute of the given name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn marker<N>(name: N) -> Self
    where
        N: Into<Name>,
    {
        Self { name: name.into() }
    }
}

/// The attribute Σ attached to a symbol: a set of markers, erased by the
/// value decoder and read by the attribute decoder.
///
/// Kept in declaration order, which is small and is provenance; membership
/// tests scan linearly.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Attrs
{
    /// The markers, in declaration order.
    pub markers: Box<[Attr]>,
}

impl Attrs
{
    /// The empty attribute Σ.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn empty() -> Self
    {
        Self {
            markers: Box::default(),
        }
    }

    /// An attribute Σ from an ordered marker collection.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<M>(markers: M) -> Self
    where
        M: Into<Box<[Attr]>>,
    {
        Self {
            markers: markers.into(),
        }
    }

    /// Whether the Σ carries no markers.
    ///
    /// # Specification
    /// - ensures: positive exactly when no marker is declared.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, singleton and duplicate-marker collections
    ///   separate an inverted emptiness verdict and an incorrect count test.
    /// - witness: `code::tests::attribute_membership_scans_markers`
    #[inline]
    #[must_use]
    #[spec(ensures: |empty| bool::from(empty) == self.markers.is_empty())]
    pub fn is_empty(&self) -> AttributeEmptiness
    {
        AttributeEmptiness::from(self.markers.is_empty())
    }

    /// Whether a marker of the given name is present.
    ///
    /// # Specification
    /// - ensures: positive exactly when some marker's name is `name`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and populated collections, first and last
    ///   positions, repeated names and absent names expose skipped positions,
    ///   inverted membership and an incorrect uniqueness requirement.
    /// - witness: `code::tests::attribute_membership_scans_markers`
    #[inline]
    #[must_use]
    #[spec(ensures: |present| bool::from(present)
        == self.markers.iter().any(|attr| attr.name.as_ref() == name.as_ref()))]
    pub fn contains(
        &self,
        name: NameRef<'_>,
    ) -> AttributePresence
    {
        AttributePresence::from(
            self.markers
                .iter()
                .any(|attr| attr.name.as_ref() == name.as_ref()),
        )
    }
}

/// The sort of an atom a [`Code::bind`] abstracts over.
///
/// The sort stays symbolic, by name; interpreting `bind A T` as an
/// atom-abstraction functor is the consumer's.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct AtomSort
{
    /// The atom sort's name.
    pub name: Name,
}

impl AtomSort
{
    /// An atom sort of the given name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn named<N>(name: N) -> Self
    where
        N: Into<Name>,
    {
        Self { name: name.into() }
    }
}

/// One node head of a code.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum CodeHead<G>
{
    /// `1`.
    Unit,
    /// `var S`, naming its sort.
    Var(Name),
    /// `A × B`.
    Prod,
    /// `A + B`.
    Sum,
    /// A leaf field over a value type, with its grade and attribute Σ.
    Field(ValueTypeRef, G, Attrs),
    /// `⟨a⟩T` over an atom sort.
    Bind(AtomSort),
}

impl<G> Head for CodeHead<G>
{
    /// The former's number of sub-codes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        ArgumentCount::from(match *self {
            | Self::Unit | Self::Var(_) | Self::Field(..) => 0_usize,
            | Self::Bind(_) => 1_usize,
            | Self::Prod | Self::Sum => 2_usize,
        })
    }
}

/// A first-order description code: one constructor's payload shape.
///
/// The fragment is `{1, var, ×, σ}` ([`Self::unit`], [`Self::var`],
/// [`Self::prod`], [`Self::sum`]) plus the leaf decorations ([`Self::field`],
/// [`Self::bind`]). It is finitary and higher-order-free, so structural
/// equality is decidable whenever the grade's is: [`Code`] derives total
/// equality and hashing, keyed on by content addressing and compared by
/// matching modulo. `G` is the grade a field carries, the consumer's own.
///
/// # Adequacy
/// - hypothesis: L3 — the six formers are distinguished by the equality
///   witness: structurally identical codes are equal, and codes differing in a
///   single leaf, grade, factor order, sort index or former are unequal; a
///   hash-map lookup recovers an entry only under an equal code.
/// - witness: `code::tests::decidable_equality_distinguishes_every_variant`
/// - witness: `code::tests::code_is_usable_as_a_hash_map_key`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Code<G>(Tree<CodeHead<G>>);

impl<G> Code<G>
{
    /// The unit code `1`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unit() -> Self
    {
        Self(Tree::leaf(CodeHead::Unit))
    }

    /// The recursive-occurrence code `var S`, targeting the sort named `sort`.
    ///
    /// The sort is the sort index of the description universe: a
    /// multi-sorted signature is one description over a sort set, and a
    /// recursive occurrence names the sort it targets; in a single-sort block
    /// the index is the block's own name. Membership in the declared sort set
    /// is checked by [`check_desc`](crate::check_desc).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn var<S>(sort: S) -> Self
    where
        S: Into<Name>,
    {
        Self(Tree::leaf(CodeHead::Var(sort.into())))
    }

    /// The product code `left × right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn prod(
        left: Self,
        right: Self,
    ) -> Self
    {
        Self(Tree::node(CodeHead::Prod, vec![left.0, right.0]))
    }

    /// The inline sum code `left + right`.
    ///
    /// A declared datatype's primary tag is its constructor table; this
    /// former is an inline sum, used to retrofit builtin sums.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sum(
        left: Self,
        right: Self,
    ) -> Self
    {
        Self(Tree::node(CodeHead::Sum, vec![left.0, right.0]))
    }

    /// A leaf field code over a value type, with its grade and attribute Σ.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn field(
        ty: ValueTypeRef,
        grade: G,
        attrs: Attrs,
    ) -> Self
    {
        Self(Tree::leaf(CodeHead::Field(ty, grade, attrs)))
    }

    /// An atom-abstraction code `⟨sort⟩body`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn bind(
        sort: AtomSort,
        body: Self,
    ) -> Self
    {
        Self(Tree::node(CodeHead::Bind(sort), vec![body.0]))
    }

    /// Fold a left-to-right field list into a right-nested product.
    ///
    /// # Specification
    /// - requires: `fields` are a constructor's field codes, in source order.
    /// - ensures: `[]` ↦ `1`, `[f]` ↦ `f`, `[f, g, h]` ↦ `f × (g × h)`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty, singleton and three-field lists pin exact
    ///   unit and singleton bases and a right-nested ordered product; extra
    ///   unit tails, omitted fields, reversal and left association differ.
    /// - witness: `code::tests::product_of_folds_right_nested_with_unit_and_singleton_bases`
    #[inline]
    #[must_use]
    #[spec(
        captures: [
            field_nodes = fields.iter().fold(0_usize, |count, field| {
                count.saturating_add(usize::from(field.0.to_ref().size()))
            }),
            field_count = fields.len(),
        ],
        ensures: |ref product| usize::from(product.0.to_ref().size())
            == field_nodes.saturating_add(field_count.saturating_sub(1)).max(1)
            && (field_count < 2 || matches!(product.view(), CodeView::Prod(_))),
    )]
    pub fn product_of(fields: Vec<Self>) -> Self
    {
        let mut fields = fields.into_iter().rev();
        let Some(mut product) = fields.next()
        else {
            return Self::unit();
        };
        for field in fields {
            product = Self::prod(field, product);
        }
        product
    }

    /// Whether this code lies in the decidable first-order fragment.
    ///
    /// The type cannot represent a higher-order code, so the fragment
    /// invariant holds by construction; the method is the executable
    /// statement of that property, not a runtime gate.
    ///
    /// # Specification
    /// - ensures: positive for every code.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L0 — no former represents a higher-order code. L3 — an
    ///   atom-abstraction, at the binding boundary, must report the positive
    ///   fragment verdict; replacing that report with false fails the witness.
    /// - witness: `code::tests::recursion_and_fragment_predicates_hold`
    #[inline]
    #[must_use]
    #[spec(ensures: |status| bool::from(status))]
    pub fn is_first_order(&self) -> FirstOrderStatus
    {
        FirstOrderStatus::from(true)
    }

    /// Whether this code contains a recursive occurrence, so the constructor
    /// it describes is recursive.
    ///
    /// # Specification
    /// - ensures: positive exactly when some node is a [`Self::var`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bare and nested recursive occurrences, repeated sorts
    ///   and a plain field separate omitted descendants, incorrect
    ///   deduplication and confusing a field type with a recursive occurrence.
    /// - witness: `code::tests::recursion_and_fragment_predicates_hold`
    /// - witness: `code::tests::recursive_sorts_preserve_order_and_repetition`
    #[inline]
    #[must_use]
    #[spec(ensures: |recursive| bool::from(recursive) == self.recursive_sorts().next().is_some())]
    pub fn is_recursive(&self) -> RecursiveStatus
    {
        RecursiveStatus::from(self.0.heads().any(|head| matches!(*head, CodeHead::Var(_))))
    }

    /// The sorts the code's recursive occurrences target, left to right.
    ///
    /// # Specification
    /// - ensures: one item per [`Self::var`] node, in left-to-right order.
    /// - panics: none.
    /// - executable: none — the backend places the opaque iterator return type
    ///   in a closure signature, which Rust rejects; observing its full
    ///   sequence would also consume the iterator before returning it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and nested code trees are observed by exact
    ///   sort sequences; left/right reversal, lost descendants, deduplication
    ///   and mistaking a field's type head for recursion change those
    ///   sequences.
    /// - witness: `wellformed::tests::the_sorting_discipline_indexes_the_description`
    /// - witness: `code::tests::recursive_sorts_preserve_order_and_repetition`
    #[inline]
    pub fn recursive_sorts(&self) -> impl Iterator<Item = &Name>
    {
        self.0.to_ref().preorder().filter_map(|head| match *head {
            | CodeHead::Var(ref sort) => Some(sort),
            | CodeHead::Unit
            | CodeHead::Prod
            | CodeHead::Sum
            | CodeHead::Field(..)
            | CodeHead::Bind(_) => None,
        })
    }

    /// The code as a borrowed node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(&self) -> CodeNode<'_, G>
    {
        CodeNode(self.0.to_ref())
    }

    /// The code's former and sub-codes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> CodeView<'_, G>
    {
        self.to_node().view()
    }
}

/// A borrowed node of a [`Code`].
#[repr(transparent)]
#[derive(Debug)]
pub struct CodeNode<'code, G>(TreeRef<'code, CodeHead<G>>);

impl<G> Clone for CodeNode<'_, G>
{
    /// Copies the borrow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        *self
    }
}

impl<G> Copy for CodeNode<'_, G>
{
}

impl<'code, G> CodeNode<'code, G>
{
    /// The node's former and sub-codes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(self) -> CodeView<'code, G>
    {
        let args = CodeArgs(self.0.children());
        match *self.0.head() {
            | CodeHead::Unit => CodeView::Unit,
            | CodeHead::Var(ref sort) => CodeView::Var(sort),
            | CodeHead::Prod => CodeView::Prod(args),
            | CodeHead::Sum => CodeView::Sum(args),
            | CodeHead::Field(ref ty, ref grade, ref attrs) => CodeView::Field { ty, grade, attrs },
            | CodeHead::Bind(ref sort) => CodeView::Bind { sort, body: args },
        }
    }

    /// An owned copy of the node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_code(self) -> Code<G>
    where
        G: Clone,
    {
        Code(self.0.to_tree())
    }
}

/// The former and sub-codes of one code node.
#[derive(Debug)]
pub enum CodeView<'code, G>
{
    /// `1`.
    Unit,
    /// `var S`, naming the sort it targets.
    Var(&'code Name),
    /// `A × B`: the two factors, left to right.
    Prod(CodeArgs<'code, G>),
    /// `A + B`: the two summands, left to right.
    Sum(CodeArgs<'code, G>),
    /// A leaf field.
    Field
    {
        /// The field's symbolic value type.
        ty: &'code ValueTypeRef,
        /// The field's grade.
        grade: &'code G,
        /// The field's attribute Σ.
        attrs: &'code Attrs,
    },
    /// `⟨a⟩T`.
    Bind
    {
        /// The atom sort abstracted over.
        sort: &'code AtomSort,
        /// The body, the one sub-code.
        body: CodeArgs<'code, G>,
    },
}

/// The sub-codes of a code node, left to right.
#[repr(transparent)]
#[derive(Debug)]
pub struct CodeArgs<'code, G>(Children<'code, CodeHead<G>>);

impl<G> Clone for CodeArgs<'_, G>
{
    /// Copies the cursor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        Self(self.0.clone())
    }
}

impl<'code, G> Iterator for CodeArgs<'code, G>
{
    type Item = CodeNode<'code, G>;

    /// The next sub-code.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(CodeNode)
    }

    /// The exact number of remaining sub-codes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        self.0.size_hint()
    }
}

impl<G> ExactSizeIterator for CodeArgs<'_, G>
{
}

#[cfg(test)]
mod tests
{
    extern crate std;

    use std::collections::HashMap;

    use super::*;
    use crate::test_support::Grade;

    /// A `Maybe`-shaped payload code for a `Some(x: a)` constructor.
    ///
    /// # Specification
    /// trivial.
    fn some_code() -> Code<Grade>
    {
        Code::field(ValueTypeRef::param("a"), Grade::One, Attrs::empty())
    }

    #[test]
    fn product_of_folds_right_nested_with_unit_and_singleton_bases()
    {
        assert_eq!(Code::<Grade>::unit(), Code::product_of(vec![]), "empty ↦ 1");
        assert_eq!(
            Code::<Grade>::var("Nat"),
            Code::product_of(vec![Code::var("Nat")]),
            "singleton ↦ the field itself"
        );
        assert_eq!(
            Code::product_of(vec![Code::unit(), Code::var("Nat"), some_code()]),
            Code::prod(Code::unit(), Code::prod(Code::var("Nat"), some_code())),
            "n-ary ↦ right-nested product"
        );
    }

    #[test]
    fn decidable_equality_distinguishes_every_variant()
    {
        for code in [
            Code::unit(),
            Code::var("Nat"),
            Code::prod(Code::var("Nat"), Code::unit()),
            Code::sum(Code::unit(), Code::unit()),
            some_code(),
            Code::bind(AtomSort::named("x"), Code::var("Nat")),
        ] {
            assert_eq!(code.clone(), code, "equality is reflexive");
        }
        assert_ne!(Code::<Grade>::unit(), Code::var("Nat"), "1 ≠ var");
        assert_ne!(
            Code::<Grade>::var("Nat"),
            Code::var("Tree"),
            "the sort index is significant: recursive occurrences of different sorts are \
             different codes"
        );
        assert_ne!(
            Code::<Grade>::prod(Code::var("Nat"), Code::unit()),
            Code::sum(Code::var("Nat"), Code::unit()),
            "× ≠ σ at the same children"
        );
        assert_ne!(
            Code::<Grade>::prod(Code::var("Nat"), Code::unit()),
            Code::prod(Code::unit(), Code::var("Nat")),
            "factor order matters"
        );
        let graded = Code::field(ValueTypeRef::param("a"), Grade::Omega, Attrs::empty());
        assert_ne!(some_code(), graded, "the grade decoration is significant");
        let primed = Code::field(
            ValueTypeRef::prim(PrimTy::Integer),
            Grade::One,
            Attrs::empty(),
        );
        assert_ne!(some_code(), primed, "the field's value type is significant");
    }

    #[test]
    fn code_is_usable_as_a_hash_map_key()
    {
        // Content addressing interns on code equality; a hash map keyed by a
        // code witnesses `Eq + Hash`.
        let mut table: HashMap<Code<Grade>, u32> = HashMap::new();
        table.insert(some_code(), 7_u32);
        assert_eq!(
            Some(7_u32),
            table.get(&some_code()).copied(),
            "a structurally identical code recovers its entry"
        );
        assert_eq!(
            None,
            table.get(&Code::var("Nat")).copied(),
            "a distinct code misses"
        );
    }

    #[test]
    fn recursion_and_fragment_predicates_hold()
    {
        assert!(
            bool::from(Code::<Grade>::var("Nat").is_recursive()),
            "var is recursive"
        );
        assert!(
            bool::from(Code::prod(some_code(), Code::var("Nat")).is_recursive()),
            "recursion under a product is detected"
        );
        assert!(
            !bool::from(some_code().is_recursive()),
            "a plain field is non-recursive"
        );
        assert!(
            bool::from(
                Code::<Grade>::bind(AtomSort::named("x"), Code::var("Nat")).is_first_order()
            ),
            "every code is first-order by construction"
        );
    }

    #[test]
    fn primitive_labels_round_trip()
    {
        for (prim, spelling) in [
            (PrimTy::Integer, "Integer"),
            (PrimTy::Boolean, "Boolean"),
            (PrimTy::Unit, "Unit"),
            (PrimTy::StringTy, "String"),
            (PrimTy::Char, "Char"),
            (PrimTy::U32, "u32"),
            (PrimTy::U64, "u64"),
            (PrimTy::I32, "i32"),
            (PrimTy::I64, "i64"),
            (PrimTy::F32, "f32"),
            (PrimTy::F64, "f64"),
            (PrimTy::Unknown, "Unknown"),
        ] {
            assert_eq!(prim.label().as_ref(), spelling);
            assert_eq!(
                PrimTy::from_label(NameRef::from(spelling)),
                Maybe::Present(prim)
            );
        }
        for spelling in ["", "NatOp", "integer", "U32", "u16"] {
            assert_eq!(
                PrimTy::from_label(NameRef::from(spelling)),
                Maybe::Absent(primitive_label::Absent::Declared)
            );
        }
    }

    #[test]
    fn attribute_membership_scans_markers()
    {
        for names in [&[][..], &["ctor"][..], &["ctor", "assoc", "ctor"][..]] {
            let attrs = Attrs::new(names.iter().copied().map(Attr::marker).collect::<Vec<_>>());
            assert_eq!(bool::from(attrs.is_empty()), names.is_empty());
            for name in ["ctor", "assoc", "infix", ""] {
                assert_eq!(
                    bool::from(attrs.contains(NameRef::from(name))),
                    names.contains(&name)
                );
            }
        }
    }

    #[test]
    fn type_heads_ignore_arguments_but_preserve_head_spelling()
    {
        for (ty, expected) in [
            (ValueTypeRef::param("a"), "a"),
            (ValueTypeRef::prim(PrimTy::StringTy), "String"),
            (ValueTypeRef::ctor("Nat", []), "Nat"),
            (
                ValueTypeRef::ctor("List", [ValueTypeRef::param("a")]),
                "List",
            ),
        ] {
            assert_eq!(ty.head_name().as_ref(), expected);
        }
    }

    #[test]
    fn recursive_sorts_preserve_order_and_repetition()
    {
        let field = Code::field(ValueTypeRef::ctor("Nat", []), Grade::One, Attrs::empty());
        assert_eq!(
            field.recursive_sorts().collect::<Vec<_>>(),
            Vec::<&Name>::new()
        );
        assert_eq!(
            Code::<Grade>::unit().recursive_sorts().collect::<Vec<_>>(),
            Vec::<&Name>::new()
        );
        let code = Code::sum(
            Code::prod(Code::var("Left"), field),
            Code::bind(
                AtomSort::named("a"),
                Code::prod(Code::var("Right"), Code::var("Left")),
            ),
        );
        assert_eq!(
            code.recursive_sorts().map(Name::as_ref).collect::<Vec<_>>(),
            ["Left", "Right", "Left"]
        );
        assert!(bool::from(code.is_recursive()));
    }
}
