//! Generic programs over descriptions: one program driven by a [`SignDesc`]
//! and its [`Code`]s, covering declared data and retrofitted builtins
//! uniformly.
//!
//! * [`generic_eq`]: structural equality of two [`DescValue`]s, guided by the
//!   description;
//! * [`serialize_value`]: a canonical, deterministic byte encoding of a
//!   [`DescValue`], guided by the description;
//! * [`serialize_desc`]: a canonical textual rendering of the description's
//!   `sign` normal form.
//!
//! A [`DescValue`] is a generic value of a described datatype: a constructor
//! tag plus a [`Payload`] shaped by that constructor's [`Code`]. Recursive
//! occurrences ([`Code::var`]) nest a whole value, tagged again, which is why
//! the generic programs are driven by the [`SignDesc`] (the σ tag), not a bare
//! [`Code`].
//!
//! [`Code`]: crate::Code
//! [`Code::var`]: crate::Code::var

use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::arity::SortRef;
use crate::boundary::ConstructorTag;
use crate::boundary::GenericEquality;
use crate::boundary::LeafBytes;
use crate::boundary::SerializedDescText;
use crate::boundary::SerializedValueBytes;
use crate::code::CodeNode;
use crate::code::CodeView;
use crate::code::Name;
use crate::desc::OperDesc;
use crate::desc::SignDesc;
use crate::elaborate::PortFace;
use crate::elaborate::RewritePort;
use crate::rule::RuleFace;
use crate::tree::ArgumentCount;
use crate::tree::Children;
use crate::tree::Head;
use crate::tree::Tree;
use crate::tree::TreeRef;

/// Which side of an inline sum ([`Code::sum`]) a value injects into.
///
/// [`Code::sum`]: crate::Code::sum
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side
{
    /// The left summand `A` of `A + B`.
    Left,
    /// The right summand `B` of `A + B`.
    Right,
}

/// One node head of a payload.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum PayloadHead
{
    /// The unit payload.
    Unit,
    /// A recursive occurrence: a value of constructor tag, whose payload is
    /// the one child.
    Rec(ConstructorTag),
    /// A product of the two children.
    Pair,
    /// An injection of the one child into a side of an inline sum.
    Inj(Side),
    /// A leaf field's opaque value bytes.
    Leaf(LeafBytes),
    /// An atom-abstraction over the bound atom's name; the body is the one
    /// child.
    Abs(Name),
}

impl Head for PayloadHead
{
    /// The former's number of sub-payloads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        ArgumentCount::from(match *self {
            | Self::Unit | Self::Leaf(_) => 0_usize,
            | Self::Rec(_) | Self::Inj(_) | Self::Abs(_) => 1_usize,
            | Self::Pair => 2_usize,
        })
    }
}

/// The payload of one constructor, shaped by its [`Code`](crate::Code).
///
/// Each former mirrors a code former: [`Self::unit`] for `1`, [`Self::rec`]
/// for `var` (a nested value of the described datatype), [`Self::pair`] for
/// `×`, [`Self::inj`] for an inline `σ`, [`Self::leaf`] for a field (the
/// value's opaque bytes), and [`Self::abs`] for an atom-abstraction. Held as
/// one flat table, so a value of any depth is built, compared, walked and
/// dropped without recursion.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Payload(Tree<PayloadHead>);

impl Payload
{
    /// The unit payload, for `1`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unit() -> Self
    {
        Self(Tree::leaf(PayloadHead::Unit))
    }

    /// A recursive occurrence carrying a whole value, for `var`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rec(value: DescValue) -> Self
    {
        Self(Tree::node(PayloadHead::Rec(value.ctor), vec![
            value.payload.0,
        ]))
    }

    /// A product of two payloads, for `×`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pair(
        first: Self,
        second: Self,
    ) -> Self
    {
        Self(Tree::node(PayloadHead::Pair, vec![first.0, second.0]))
    }

    /// An injection into one side of an inline sum, for `+`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn inj(
        side: Side,
        body: Self,
    ) -> Self
    {
        Self(Tree::node(PayloadHead::Inj(side), vec![body.0]))
    }

    /// A leaf field's opaque value bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn leaf<B>(bytes: B) -> Self
    where
        B: Into<LeafBytes>,
    {
        Self(Tree::leaf(PayloadHead::Leaf(bytes.into())))
    }

    /// An atom-abstraction over the named atom, for `⟨a⟩T`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn abs<N>(
        atom: N,
        body: Self,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self(Tree::node(PayloadHead::Abs(atom.into()), vec![body.0]))
    }

    /// The payload as a borrowed node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(&self) -> PayloadNode<'_>
    {
        PayloadNode(self.0.to_ref())
    }

    /// The payload's former and sub-payloads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> PayloadView<'_>
    {
        self.to_node().view()
    }
}

/// A borrowed node of a [`Payload`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PayloadNode<'value>(TreeRef<'value, PayloadHead>);

impl<'value> PayloadNode<'value>
{
    /// The node's former and sub-payloads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(self) -> PayloadView<'value>
    {
        let args = PayloadArgs(self.0.children());
        match *self.0.head() {
            | PayloadHead::Unit => PayloadView::Unit,
            | PayloadHead::Rec(ctor) => PayloadView::Rec {
                ctor,
                payload: args,
            },
            | PayloadHead::Pair => PayloadView::Pair(args),
            | PayloadHead::Inj(side) => PayloadView::Inj { side, body: args },
            | PayloadHead::Leaf(ref bytes) => PayloadView::Leaf(bytes),
            | PayloadHead::Abs(ref atom) => PayloadView::Abs { atom, body: args },
        }
    }

    /// An owned copy of the node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_payload(self) -> Payload
    {
        Payload(self.0.to_tree())
    }
}

/// The former and sub-payloads of one payload node.
#[derive(Clone, Debug)]
pub enum PayloadView<'value>
{
    /// The unit payload.
    Unit,
    /// A recursive occurrence.
    Rec
    {
        /// The nested value's constructor tag.
        ctor: ConstructorTag,
        /// The nested value's payload, the one sub-payload.
        payload: PayloadArgs<'value>,
    },
    /// A product: the two factors, left to right.
    Pair(PayloadArgs<'value>),
    /// An injection into an inline sum.
    Inj
    {
        /// The side injected into.
        side: Side,
        /// The injected payload, the one sub-payload.
        body: PayloadArgs<'value>,
    },
    /// A leaf field's opaque value bytes.
    Leaf(&'value LeafBytes),
    /// An atom-abstraction.
    Abs
    {
        /// The bound atom's name.
        atom: &'value Name,
        /// The body, the one sub-payload.
        body: PayloadArgs<'value>,
    },
}

/// The sub-payloads of a payload node, left to right.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct PayloadArgs<'value>(Children<'value, PayloadHead>);

impl<'value> Iterator for PayloadArgs<'value>
{
    type Item = PayloadNode<'value>;

    /// The next sub-payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(PayloadNode)
    }

    /// The exact number of remaining sub-payloads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for PayloadArgs<'_>
{
}

/// A generic value of a described datatype: a constructor tag (an index into
/// [`SignDesc::ctors`]) plus its [`Payload`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DescValue
{
    /// The constructor index into [`SignDesc::ctors`].
    pub ctor: ConstructorTag,
    /// The constructor's payload, shaped by that constructor's code.
    pub payload: Payload,
}

impl DescValue
{
    /// A value of constructor `ctor` with the given payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        ctor: ConstructorTag,
        payload: Payload,
    ) -> Self
    {
        Self { ctor, payload }
    }
}

quenchant_shape::reason_enum! {
    /// Why a constructor tag names no constructor of a description.
    mod constructor_tag {
        /// The reason the tag names nothing.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The tag indexes past the description's constructor table: the
            /// value is mis-built.
            OutOfRange,
        }
    }
}

/// The code of the constructor `ctor` names in `desc`.
///
/// # Specification
/// - ensures: the addressed constructor's code when the tag is in range,
///   otherwise the explicit out-of-range absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid tags, the first absent tag and the largest tag are
///   observed through structural equality and exact encoded bytes; off-by-one
///   indexing or treating absence as a unit payload changes them.
/// - witness: `generic::tests::generic_eq_is_description_driven_structural`
/// - witness: `generic::tests::malformed_values_and_out_of_range_tags_have_defined_observations`
#[spec(ensures: |ref code| matches!(*code, Maybe::Present(_)) == (usize::from(ctor) < desc.ctors.len()))]
fn ctor_code<G>(
    desc: &SignDesc<G>,
    ctor: ConstructorTag,
) -> Maybe<CodeNode<'_, G>, constructor_tag::Absent>
{
    match desc.ctors.get(usize::from(ctor)) {
        | Some(described) => Maybe::Present(described.code.to_node()),
        | None => Maybe::Absent(constructor_tag::Absent::OutOfRange),
    }
}

quenchant_shape::reason_enum! {
    /// Why a port carries no authored name.
    mod port_name {
        /// The reason the port is anonymous.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The name is empty or one of the minted underscore-led
            /// placeholders the named-port normal form assigns to unnamed
            /// tuple entries.
            Anonymous,
        }
    }
}

/// The port's authored name.
///
/// # Specification
/// - ensures: the name unless it is empty or underscore-led, which marks a
///   minted placeholder.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and underscore-led names are separated from an
///   authored name by exact presence and rendered port text; omitting either
///   anonymous-name condition or stripping a real name changes the result.
/// - witness: `generic::tests::port_rendering_distinguishes_authored_and_placeholder_names`
#[spec(ensures: |ref name| match *name {
    | Maybe::Present(name) => name == &port.name && !name.as_ref().is_empty() && !name.as_ref().starts_with('_'),
    | Maybe::Absent(_) => port.name.as_ref().is_empty() || port.name.as_ref().starts_with('_'),
})]
fn authored_name(port: &SortRef) -> Maybe<&Name, port_name::Absent>
{
    let name = port.name.as_ref();
    if name.is_empty() || name.starts_with('_') {
        Maybe::Absent(port_name::Absent::Anonymous)
    }
    else {
        Maybe::Present(&port.name)
    }
}

/// Generic structural equality of two values of a described datatype, guided
/// by `desc`.
///
/// # Specification
/// - requires: `left` and `right` are intended values of `desc`.
/// - ensures: positive exactly when the two values agree constructor by
///   constructor and, through every nested occurrence, payload by payload; a
///   value whose shape does not match its constructor's code (a mis-built
///   value) compares unequal, as does an out-of-range constructor tag.
/// - panics: none.
/// - intension: one worklist of (code, payload, payload) triples; a recursive
///   occurrence re-enters at the nested constructor's code.
///
/// # Adequacy
/// - hypothesis: L3 — valid values, unequal tags/leaves/atoms, opposite sum
///   injections, recursive differences, malformed payloads and out-of-range
///   tags are observed by exact equality verdicts; skipped shape checks or
///   comparing only a prefix changes those verdicts.
/// - witness: `generic::tests::generic_eq_is_description_driven_structural`
/// - witness: `generic::tests::generic_eq_recurses_through_var`
/// - witness: `generic::tests::malformed_values_and_out_of_range_tags_have_defined_observations`
/// - witness: `generic::tests::sum_and_abstraction_encodings_pin_sides_names_and_lengths`
#[inline]
#[must_use]
#[spec(ensures: |equal| !bool::from(equal)
    || (left == right && usize::from(left.ctor) < desc.ctors.len()))]
pub fn generic_eq<G>(
    desc: &SignDesc<G>,
    left: &DescValue,
    right: &DescValue,
) -> GenericEquality
{
    if left.ctor != right.ctor {
        return GenericEquality::from(false);
    }
    let Maybe::Present(code) = ctor_code(desc, left.ctor)
    else {
        // An out-of-range tag is a mis-built value: unequal, never a panic.
        return GenericEquality::from(false);
    };
    let mut pending = vec![(code, left.payload.to_node(), right.payload.to_node())];
    while let Some((code, lhs, rhs)) = pending.pop() {
        match (code.view(), lhs.view(), rhs.view()) {
            | (CodeView::Unit, PayloadView::Unit, PayloadView::Unit) => {},
            | (
                CodeView::Var(_),
                PayloadView::Rec {
                    ctor: left_ctor,
                    payload: mut left_inner,
                },
                PayloadView::Rec {
                    ctor: right_ctor,
                    payload: mut right_inner,
                },
            ) => {
                if left_ctor != right_ctor {
                    return GenericEquality::from(false);
                }
                let (Maybe::Present(inner_code), Some(left_inner), Some(right_inner)) = (
                    ctor_code(desc, left_ctor),
                    left_inner.next(),
                    right_inner.next(),
                )
                else {
                    return GenericEquality::from(false);
                };
                pending.push((inner_code, left_inner, right_inner));
            },
            | (CodeView::Prod(factors), PayloadView::Pair(lefts), PayloadView::Pair(rights)) => {
                if factors.len() != lefts.len() || lefts.len() != rights.len() {
                    return GenericEquality::from(false);
                }
                let triples: Vec<_> = factors.zip(lefts).zip(rights).collect();
                pending.extend(
                    triples
                        .into_iter()
                        .rev()
                        .map(|((factor, first), second)| (factor, first, second)),
                );
            },
            | (
                CodeView::Sum(mut summands),
                PayloadView::Inj {
                    side: left_side,
                    body: mut left_body,
                },
                PayloadView::Inj {
                    side: right_side,
                    body: mut right_body,
                },
            ) => {
                if left_side != right_side {
                    return GenericEquality::from(false);
                }
                let summand = match left_side {
                    | Side::Left => summands.next(),
                    | Side::Right => summands.nth(1),
                };
                let (Some(summand), Some(left_body), Some(right_body)) =
                    (summand, left_body.next(), right_body.next())
                else {
                    return GenericEquality::from(false);
                };
                pending.push((summand, left_body, right_body));
            },
            | (
                CodeView::Field { .. },
                PayloadView::Leaf(left_bytes),
                PayloadView::Leaf(right_bytes),
            ) if left_bytes == right_bytes => {},
            | (
                CodeView::Bind {
                    body: mut body_code,
                    ..
                },
                PayloadView::Abs {
                    atom: left_atom,
                    body: mut left_body,
                },
                PayloadView::Abs {
                    atom: right_atom,
                    body: mut right_body,
                },
            ) if left_atom == right_atom => {
                let (Some(body_code), Some(left_body), Some(right_body)) =
                    (body_code.next(), left_body.next(), right_body.next())
                else {
                    return GenericEquality::from(false);
                };
                pending.push((body_code, left_body, right_body));
            },
            // Any code/payload shape mismatch: a mis-built value compares
            // unequal.
            | _ => return GenericEquality::from(false),
        }
    }
    GenericEquality::from(true)
}

/// Generic serialization of a value to a canonical, deterministic byte
/// encoding, guided by `desc`.
///
/// The encoding is a tag-and-payload walk: the constructor index as a
/// little-endian `u32`, then each field's bytes in code order. A product
/// concatenates, an inline sum emits a side byte (`0` left, `1` right) then
/// the injected payload, a leaf emits its length as a little-endian `u32`
/// then its bytes, an atom-abstraction emits the atom's name the same way
/// then its body, and a recursive occurrence emits the nested value whole. It
/// is deterministic — the same value always encodes to the same bytes — which
/// is what content addressing and equality-by-bytes need.
///
/// # Specification
/// - requires: `value` is an intended value of `desc`.
/// - ensures: `value`'s canonical encoding in a fresh buffer; values
///   [`generic_eq`] relates encode to equal bytes.
/// - panics: none; a mis-built value encodes what structure it has (an
///   out-of-range tag encodes just the tag).
///
/// # Adequacy
/// - hypothesis: L3 — exact bytes for empty/nonempty leaves, both injection
///   sides and atom names pin tags, lengths and order. Malformed payloads and
///   first-past/largest tags pin partial encoding; wrong endian, side or length
///   bytes, omitted names and encoding a refused payload differ.
/// - witness: `generic::tests::serialization_is_deterministic_and_agrees_with_equality`
/// - witness: `generic::tests::malformed_values_and_out_of_range_tags_have_defined_observations`
/// - witness: `generic::tests::sum_and_abstraction_encodings_pin_sides_names_and_lengths`
#[inline]
#[must_use]
#[spec(ensures: |ref bytes| bytes.as_ref().starts_with(
    &u32::try_from(usize::from(value.ctor)).unwrap_or(u32::MAX).to_le_bytes()
))]
pub fn serialize_value<G>(
    desc: &SignDesc<G>,
    value: &DescValue,
) -> SerializedValueBytes
{
    /// One step of the encoding worklist.
    enum EncodeTask<'value, G>
    {
        /// Encode a tagged value: its tag, then its payload.
        Value(ConstructorTag, PayloadNode<'value>),
        /// Encode a payload against its code.
        Payload(CodeNode<'value, G>, PayloadNode<'value>),
    }

    let push_counted = |out: &mut Vec<u8>, bytes: &[u8]| {
        let len = u32::try_from(bytes.len()).unwrap_or(u32::MAX);
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(bytes);
    };
    let mut out: Vec<u8> = Vec::new();
    let mut stack: Vec<EncodeTask<'_, G>> =
        vec![EncodeTask::Value(value.ctor, value.payload.to_node())];
    while let Some(task) = stack.pop() {
        match task {
            | EncodeTask::Value(ctor, payload) => {
                let tag = u32::try_from(usize::from(ctor)).unwrap_or(u32::MAX);
                out.extend_from_slice(&tag.to_le_bytes());
                if let Maybe::Present(code) = ctor_code(desc, ctor) {
                    stack.push(EncodeTask::Payload(code, payload));
                }
            },
            | EncodeTask::Payload(code, payload) => match (code.view(), payload.view()) {
                | (
                    CodeView::Var(_),
                    PayloadView::Rec {
                        ctor,
                        payload: inner,
                    },
                ) => {
                    stack.extend(inner.map(|inner| EncodeTask::Value(ctor, inner)));
                },
                | (CodeView::Prod(factors), PayloadView::Pair(parts)) => {
                    let pairs: Vec<_> = factors.zip(parts).collect();
                    stack.extend(
                        pairs
                            .into_iter()
                            .rev()
                            .map(|(factor, part)| EncodeTask::Payload(factor, part)),
                    );
                },
                | (CodeView::Sum(mut summands), PayloadView::Inj { side, body }) => {
                    let summand = match side {
                        | Side::Left => {
                            out.push(0_u8);
                            summands.next()
                        },
                        | Side::Right => {
                            out.push(1_u8);
                            summands.nth(1)
                        },
                    };
                    stack.extend(
                        summand
                            .into_iter()
                            .zip(body)
                            .map(|(summand, body)| EncodeTask::Payload(summand, body)),
                    );
                },
                | (CodeView::Field { .. }, PayloadView::Leaf(bytes)) => {
                    push_counted(&mut out, bytes.as_ref());
                },
                | (
                    CodeView::Bind {
                        body: body_code, ..
                    },
                    PayloadView::Abs { atom, body },
                ) => {
                    push_counted(&mut out, atom.as_ref().as_bytes());
                    stack.extend(
                        body_code
                            .zip(body)
                            .map(|(body_code, body)| EncodeTask::Payload(body_code, body)),
                    );
                },
                // `1` contributes no bytes, as does any mis-built payload.
                | _ => {},
            },
        }
    }
    SerializedValueBytes::from(out)
}

/// Inspectable rendering of a description's `sign` normal form to canonical
/// text, in the ruled surface spelling.
///
/// Every description renders as its `sign` normal form, with the declared
/// sort set spelled first and the arrow grid's `-->` / `==>` at every arrow
/// position. The normal form's members are sorts, operations and rules only:
/// a family is declared once, whole, as a nested generator block, so
/// constructor and observation descriptors have no member spelling here and
/// the render omits them; they remain inspectable through
/// [`SignDesc::ctors`].
///
/// The rendering is deterministic and structural — an inspection notation,
/// not a surface pretty-printer. Every member is terminated by `;`, and the
/// whole description stays one line.
///
/// # Specification
/// - ensures: deterministic output for a given description: `sign` and the
///   datatype's name, its parameters in parentheses when it has any, then the
///   sorts, operations, rule faces and circuit rules in declaration order, each
///   terminated by `;`, or `{}` when there are none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — parameterized and unparameterized descriptions, no
///   members and descriptions with sorts, operations and circuit telescopes
///   have exact expected text; reordered or omitted members, added constructor
///   members, lost separators and the wrong empty-body form change it.
/// - witness: `generic::tests::desc_inspection_renders_the_structure`
/// - witness: `generic::tests::desc_inspection_omits_constructor_members`
/// - witness: `generic::tests::desc_inspection_renders_a_circuit_rule_and_its_telescope`
/// - witness: `generic::tests::telescopes_and_empty_descriptions_have_exact_delimiters`
/// - witness: `generic::tests::desc_inspection_omits_a_primitive_field_constructor`
/// - witness: `generic::tests::port_rendering_distinguishes_authored_and_placeholder_names`
/// - witness: `generic::tests::description_members_keep_their_declared_kind_order`
#[inline]
#[must_use]
#[spec(ensures: |ref text| text.as_ref().strip_prefix("sign ")
    .and_then(|body| body.strip_prefix(desc.id.name.as_ref()))
    .is_some_and(|body| body.starts_with(if desc.params.is_empty() { " {" } else { "(" }))
    && text.as_ref().ends_with(if desc.sorts.is_empty() && desc.opers.is_empty()
        && desc.rules.is_empty() && desc.circuits.is_empty() { "{}" } else { "; }" }))]
pub fn serialize_desc<G>(desc: &SignDesc<G>) -> SerializedDescText
{
    let params: Vec<String> = desc
        .params
        .iter()
        .map(|param| param.name.to_string())
        .collect();
    let params = if params.is_empty() {
        String::new()
    }
    else {
        format!("({})", params.join(", "))
    };
    let mut members: Vec<String> = Vec::new();
    for sort in &desc.sorts {
        members.push(format!("sort {} : Type", sort.name));
    }
    for oper in &desc.opers {
        members.push(render_oper_member(oper));
    }
    for rule in &desc.rules {
        members.push(format!("rule {}", render_face(rule)));
    }
    for rule in &desc.circuits {
        let telescope = render_telescope(&rule.ports);
        let separator = if telescope.is_empty() { "" } else { " " };
        members.push(format!(
            "rule {} : {telescope}{separator}{}",
            rule.name,
            render_face(&rule.sphere)
        ));
    }
    let rendered = if members.is_empty() {
        format!("sign {}{params} {{}}", desc.id.name)
    }
    else {
        format!(
            "sign {}{params} {{ {}; }}",
            desc.id.name,
            members.join("; ")
        )
    };
    SerializedDescText::from(rendered)
}

/// Render one operation as its ruled judgment-style member, in the named-port
/// normal form (`oper add : (m : Nat, n : Nat) --> (q : Nat)`); a port with
/// no authored name spells its sort bare, and a single unnamed output drops
/// its parentheses.
///
/// # Specification
/// - ensures: named-port input notation and an output tuple, except that a sole
///   anonymous output is its bare sort; both empty tuples are explicit.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one named, one anonymous and two output ports have
///   exact text; omitted parentheses, named/anonymous confusion and reversed
///   port order change the rendering.
/// - witness: `generic::tests::port_rendering_distinguishes_authored_and_placeholder_names`
#[spec(ensures: |ref text| text.strip_prefix("oper ")
    .and_then(|body| body.strip_prefix(oper.name.as_ref()))
    .is_some_and(|body| body.starts_with(" : (")) && text.contains(") --> "))]
fn render_oper_member(oper: &OperDesc) -> String
{
    let inputs: Vec<String> = oper.arity.inputs.iter().map(render_port).collect();
    let outputs: Vec<String> = oper.arity.outputs.iter().map(render_port).collect();
    let outputs = match *oper.arity.outputs {
        | [ref only] if matches!(authored_name(only), Maybe::Absent(_)) => outputs.concat(),
        | _ => format!("({})", outputs.join(", ")),
    };
    format!("oper {} : ({}) --> {outputs}", oper.name, inputs.join(", "))
}

/// Render one port (`m : Nat`), spelling the sort bare when the port carries
/// no authored name.
///
/// # Specification
/// - ensures: anonymous ports render their bare sort; authored names render as
///   the name, a colon separator and their sort.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, underscore and authored names have exact port
///   text; a spurious name, lost sort or wrong separator changes that text.
/// - witness: `generic::tests::port_rendering_distinguishes_authored_and_placeholder_names`
#[spec(ensures: |ref text| match authored_name(port) {
    | Maybe::Present(name) => text.strip_prefix(name.as_ref())
        .and_then(|body| body.strip_prefix(" : ")) == Some(port.sort.as_ref()),
    | Maybe::Absent(_) => text == port.sort.as_ref(),
})]
fn render_port(port: &SortRef) -> String
{
    match authored_name(port) {
        | Maybe::Present(name) => format!("{name} : {}", port.sort),
        | Maybe::Absent(port_name::Absent::Anonymous) => port.sort.to_string(),
    }
}

/// Render a circuit rule's parameter telescope: its rewrite-sorted ports,
/// each in the ruled binder spelling.
///
/// An empty telescope renders as nothing at all. A port renders at the form
/// its declaration wrote: `rule p : Nat ==> Nat` for the sorted form,
/// `rule p : x ==> x′` for the pinned one — the same `==>` a face renders
/// with.
///
/// # Specification
/// - ensures: no text for an empty telescope; otherwise ordered, comma-
///   separated rewrite binders in parentheses, preserving sorted and pinned
///   endpoint forms.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and mixed sorted/pinned telescopes have exact text;
///   spurious empty parentheses, reordering and confusing the endpoint forms
///   change that text.
/// - witness: `generic::tests::telescopes_and_empty_descriptions_have_exact_delimiters`
#[spec(ensures: |ref text| if ports.is_empty() { text.is_empty() }
    else { text.starts_with('(') && text.ends_with(')') && text.contains(" ==> ") })]
fn render_telescope(ports: &[RewritePort]) -> String
{
    if ports.is_empty() {
        return String::new();
    }
    let rendered: Vec<String> = ports
        .iter()
        .map(|port| match port.face {
            | PortFace::Sorted(ref sort) => format!("rule {} : {sort} ==> {sort}", port.name),
            | PortFace::Pinned {
                ref source,
                ref target,
            } => format!("rule {} : {source} ==> {target}", port.name),
        })
        .collect();
    format!("({})", rendered.join(", "))
}

/// Render a rule face to the inspection notation `lhs ==> rhs`.
///
/// # Specification
/// - ensures: the left and right inspection terms separated by ` ==> `.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a circuit sphere with different source and target
///   applications has exact text; a missing separator or swapped sides fails.
/// - witness: `generic::tests::desc_inspection_renders_a_circuit_rule_and_its_telescope`
#[spec(ensures: |ref text| text.contains(" ==> "))]
fn render_face(rule: &RuleFace) -> String
{
    format!("{} ==> {}", rule.lhs, rule.rhs)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::*;
    use crate::circuit::CircuitBody;
    use crate::circuit::CircuitFrame;
    use crate::circuit::CircuitNode;
    use crate::circuit::CircuitRedex;
    use crate::circuit::CircuitRule;
    use crate::circuit::FrameHead;
    use crate::circuit::derive_boundaries;
    use crate::code::Attr;
    use crate::code::Attrs;
    use crate::code::Code;
    use crate::code::PrimTy;
    use crate::code::ValueTypeRef;
    use crate::desc::CtorDesc;
    use crate::desc::DeclPolarity;
    use crate::desc::NominalId;
    use crate::desc::ParamDesc;
    use crate::desc::SurfaceSpan;
    use crate::rule::FreeTerm;
    use crate::test_support::Grade;

    #[test]
    fn generic_eq_is_description_driven_structural()
    {
        let desc = maybe_desc();
        let some_a = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"a"[..]));
        let some_a2 = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"a"[..]));
        let some_b = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"b"[..]));
        let none = DescValue::new(ConstructorTag::from(0_usize), Payload::unit());

        assert!(
            bool::from(generic_eq(&desc, &some_a, &some_a2)),
            "equal Some values agree"
        );
        assert!(
            !bool::from(generic_eq(&desc, &some_a, &some_b)),
            "Some values differing in a leaf disagree"
        );
        assert!(
            !bool::from(generic_eq(&desc, &some_a, &none)),
            "different constructors disagree"
        );
        assert!(
            bool::from(generic_eq(&desc, &none, &none)),
            "None equals None"
        );
    }

    #[test]
    fn serialization_is_deterministic_and_agrees_with_equality()
    {
        let desc = maybe_desc();
        let some_a = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"a"[..]));
        let some_a2 = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"a"[..]));
        let some_b = DescValue::new(ConstructorTag::from(1_usize), Payload::leaf(&b"b"[..]));

        assert_eq!(
            serialize_value(&desc, &some_a),
            serialize_value(&desc, &some_a2),
            "equal values encode identically"
        );
        assert_ne!(
            serialize_value(&desc, &some_a),
            serialize_value(&desc, &some_b),
            "distinct values encode differently"
        );
        // Tag 1 (LE u32) + length 1 (LE u32) + byte 'a'.
        assert_eq!(
            &[1_u8, 0, 0, 0, 1, 0, 0, 0, b'a'],
            serialize_value(&desc, &some_a).as_ref(),
            "the canonical encoding is tag-then-payload"
        );
    }

    #[test]
    fn desc_inspection_renders_the_structure()
    {
        assert_eq!(
            "sign Maybe(a) { sort Maybe : Type; }",
            serialize_desc(&maybe_desc()).as_ref(),
            "the inspection notation names the parameters and the sort set; constructors have \
             no item-level member spelling in the sign normal form"
        );
    }

    /// The `Maybe(a)` description: `None = 1`, `Some = field a`.
    ///
    /// # Specification
    /// trivial.
    fn maybe_desc() -> SignDesc<Grade>
    {
        SignDesc::new(
            NominalId::new(0_u64.into(), "Maybe"),
            [ParamDesc::new("a", Grade::One, Attrs::empty())],
            [
                CtorDesc::new("None", Code::unit(), "Maybe", Attrs::empty()),
                CtorDesc::new(
                    "Some",
                    Code::field(ValueTypeRef::param("a"), Grade::One, Attrs::empty()),
                    "Maybe",
                    Attrs::empty(),
                ),
            ],
            Vec::new(),
            Vec::new(),
            DeclPolarity::Data,
            Attrs::empty(),
        )
    }

    #[test]
    fn generic_eq_recurses_through_var()
    {
        let desc = nat_desc();
        let zero = || DescValue::new(ConstructorTag::from(0_usize), Payload::unit());
        let succ =
            |inner: DescValue| DescValue::new(ConstructorTag::from(1_usize), Payload::rec(inner));
        // 2 = Succ(Succ(Zero)).
        let two = succ(succ(zero()));
        let two_again = two.clone();
        // 1 = Succ(Zero).
        let one = succ(zero());
        assert!(
            bool::from(generic_eq(&desc, &two, &two_again)),
            "2 == 2 through var"
        );
        assert!(
            !bool::from(generic_eq(&desc, &two, &one)),
            "2 ≠ 1 through var"
        );
    }

    /// A `Nat`-like recursive description: `Zero = 1`, `Succ = var`.
    ///
    /// # Specification
    /// trivial.
    fn nat_desc() -> SignDesc<Grade>
    {
        SignDesc::new(
            NominalId::new(1_u64.into(), "Nat"),
            Vec::new(),
            [
                CtorDesc::new("Zero", Code::unit(), "Nat", Attrs::empty()),
                CtorDesc::new("Succ", Code::var("Nat"), "Nat", Attrs::empty()),
            ],
            Vec::new(),
            Vec::new(),
            DeclPolarity::Data,
            Attrs::empty(),
        )
    }

    #[test]
    fn desc_inspection_omits_constructor_members()
    {
        let desc = SignDesc::new(
            NominalId::new(0_u64.into(), "Vec"),
            [ParamDesc::new("a", Grade::One, Attrs::empty())],
            [
                CtorDesc::new("Nil", Code::unit(), "Vec", Attrs::empty()),
                CtorDesc::new(
                    "Cons",
                    Code::prod(
                        Code::field(ValueTypeRef::param("a"), Grade::One, Attrs::empty()),
                        Code::var("Vec"),
                    ),
                    "Vec",
                    Attrs::new([Attr::marker("ctor")]),
                ),
            ],
            Vec::new(),
            Vec::new(),
            DeclPolarity::Data,
            Attrs::empty(),
        );
        assert_eq!(
            "sign Vec(a) { sort Vec : Type; }",
            serialize_desc(&desc).as_ref(),
            "constructors — graded, attributed, or right-nested — carry no member spelling: \
             the item-level `data` member is retired from the sign normal form"
        );
    }

    #[test]
    fn desc_inspection_renders_a_circuit_rule_and_its_telescope()
    {
        let body = CircuitBody::new(
            [
                CircuitNode::Redex(CircuitRedex::new(
                    "p",
                    FreeTerm::var("x"),
                    FreeTerm::var("x\u{2032}"),
                    "x\u{2032}",
                )),
                CircuitNode::Frame(CircuitFrame::new(
                    FrameHead::Op("add".into()),
                    [FreeTerm::var("x\u{2032}"), FreeTerm::var("y")],
                    "z",
                )),
            ],
            "z",
        );
        let derived = derive_boundaries(&body).expect("derives");
        let rule = CircuitRule::new(
            "cong1",
            RuleFace::new(
                derived.source,
                derived.target,
                Vec::new(),
                SurfaceSpan::new(0_usize.into(), 0_usize.into()),
            ),
            body,
        )
        .with_ports([RewritePort::sorted("p", "Nat")]);
        let desc: SignDesc<Grade> = SignDesc::new(
            NominalId::new(0_u64.into(), "Nat"),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            DeclPolarity::Data,
            Attrs::empty(),
        )
        .with_circuits([rule]);
        assert_eq!(
            "sign Nat { sort Nat : Type; rule cong1 : (rule p : Nat ==> Nat) add(x, y) ==> \
             add(x\u{2032}, y); }",
            serialize_desc(&desc).as_ref(),
            "a circuit member renders its telescope and its sphere"
        );
    }

    #[test]
    fn description_members_keep_their_declared_kind_order()
    {
        let rules = [("x", "y"), ("y", "z")].map(|(left, right)| {
            RuleFace::new(
                FreeTerm::var(left),
                FreeTerm::var(right),
                [],
                SurfaceSpan::new(0_usize.into(), 0_usize.into()),
            )
        });
        let opers = ["first", "second"].map(|name| {
            OperDesc::new(
                name,
                crate::arity::BridgeArity::single_output([], SortRef::new("", "A")),
                Attrs::empty(),
            )
        });
        let circuits = ["c", "d"]
            .map(|name| CircuitRule::new(name, rules[0].clone(), CircuitBody::new([], "x")));
        let desc: SignDesc<Grade> = SignDesc::new(
            NominalId::new(0_u64.into(), "Ordered"),
            [],
            [],
            opers,
            rules,
            DeclPolarity::Data,
            Attrs::empty(),
        )
        .with_sorts([
            crate::desc::SortDesc::new("A", DeclPolarity::Data),
            crate::desc::SortDesc::new("B", DeclPolarity::Data),
        ])
        .with_circuits(circuits);
        assert_eq!(
            serialize_desc(&desc).as_ref(),
            "sign Ordered { sort A : Type; sort B : Type; oper first : () --> A; oper second : () --> A; rule x ==> y; rule y ==> z; rule c : x ==> y; rule d : x ==> y; }"
        );
    }

    #[test]
    fn telescopes_and_empty_descriptions_have_exact_delimiters()
    {
        assert_eq!(render_telescope(&[]), "");
        let ports = [
            RewritePort::sorted("p", "Nat"),
            RewritePort::pinned(
                "q",
                FreeTerm::var("x"),
                FreeTerm::op("s", [FreeTerm::var("x")]),
            ),
        ];
        assert_eq!(
            render_telescope(&ports),
            "(rule p : Nat ==> Nat, rule q : x ==> s(x))"
        );
        let desc: SignDesc<Grade> = SignDesc::new(
            NominalId::new(0_u64.into(), "Empty"),
            [],
            [],
            [],
            [],
            DeclPolarity::Data,
            Attrs::empty(),
        )
        .with_sorts([]);
        assert_eq!(serialize_desc(&desc).as_ref(), "sign Empty {}");
    }

    #[test]
    fn desc_inspection_omits_a_primitive_field_constructor()
    {
        let desc = SignDesc::new(
            NominalId::new(0_u64.into(), "Wrap"),
            Vec::new(),
            [CtorDesc::new(
                "Wrap",
                Code::field(
                    ValueTypeRef::prim(PrimTy::Integer),
                    Grade::One,
                    Attrs::empty(),
                ),
                "Wrap",
                Attrs::empty(),
            )],
            Vec::new(),
            Vec::new(),
            DeclPolarity::Data,
            Attrs::empty(),
        );
        assert_eq!(
            "sign Wrap { sort Wrap : Type; }",
            serialize_desc(&desc).as_ref(),
            "a primitive-field constructor renders no member spelling either"
        );
    }

    #[test]
    fn malformed_values_and_out_of_range_tags_have_defined_observations()
    {
        let desc = maybe_desc();
        for tag in [2_usize, usize::MAX] {
            let value = DescValue::new(ConstructorTag::from(tag), Payload::unit());
            assert!(!bool::from(generic_eq(&desc, &value, &value)));
            let expected = u32::try_from(tag).unwrap_or(u32::MAX).to_le_bytes();
            assert_eq!(serialize_value(&desc, &value).as_ref(), expected);
        }
        let malformed = DescValue::new(ConstructorTag::from(1_usize), Payload::unit());
        assert!(!bool::from(generic_eq(&desc, &malformed, &malformed)));
        assert_eq!(serialize_value(&desc, &malformed).as_ref(), [1_u8, 0, 0, 0]);
    }

    #[test]
    fn sum_and_abstraction_encodings_pin_sides_names_and_lengths()
    {
        let mut desc = maybe_desc();
        let field = Code::field(ValueTypeRef::param("a"), Grade::One, Attrs::empty());
        desc.ctors = alloc::boxed::Box::from([CtorDesc::new(
            "Sum",
            Code::sum(
                field.clone(),
                Code::bind(crate::code::AtomSort::named("Name"), field),
            ),
            "Maybe",
            Attrs::empty(),
        )]);
        let left = DescValue::new(
            ConstructorTag::from(0_usize),
            Payload::inj(Side::Left, Payload::leaf(&b""[..])),
        );
        let right = DescValue::new(
            ConstructorTag::from(0_usize),
            Payload::inj(Side::Right, Payload::abs("a", Payload::leaf(&b"b"[..]))),
        );
        let renamed = DescValue::new(
            ConstructorTag::from(0_usize),
            Payload::inj(Side::Right, Payload::abs("c", Payload::leaf(&b"b"[..]))),
        );
        assert!(bool::from(generic_eq(&desc, &left, &left)));
        assert!(bool::from(generic_eq(&desc, &right, &right)));
        assert!(!bool::from(generic_eq(&desc, &left, &right)));
        assert!(!bool::from(generic_eq(&desc, &right, &renamed)));
        assert_eq!(serialize_value(&desc, &left).as_ref(), [
            0_u8, 0, 0, 0, 0, 0, 0, 0, 0
        ]);
        assert_eq!(serialize_value(&desc, &right).as_ref(), [
            0_u8, 0, 0, 0, 1, 1, 0, 0, 0, b'a', 1, 0, 0, 0, b'b'
        ]);
    }

    #[test]
    fn port_rendering_distinguishes_authored_and_placeholder_names()
    {
        for name in ["", "_", "_0", "_private"] {
            let port = SortRef::new(name, "T");
            assert_eq!(
                authored_name(&port),
                Maybe::Absent(port_name::Absent::Anonymous)
            );
            assert_eq!(render_port(&port), "T");
        }
        let named = SortRef::new("port", "T");
        assert_eq!(authored_name(&named), Maybe::Present(&named.name));
        assert_eq!(render_port(&named), "port : T");
        for (outputs, expected) in [
            (vec![], "oper f : (x : A, B) --> ()"),
            (vec![SortRef::new("_0", "C")], "oper f : (x : A, B) --> C"),
            (
                vec![SortRef::new("y", "C")],
                "oper f : (x : A, B) --> (y : C)",
            ),
            (
                vec![SortRef::new("_0", "C"), SortRef::new("_1", "D")],
                "oper f : (x : A, B) --> (C, D)",
            ),
        ] {
            let oper = OperDesc::new(
                "f",
                crate::arity::BridgeArity::new(
                    [SortRef::new("x", "A"), SortRef::new("_0", "B")],
                    [],
                    [],
                    [],
                    outputs,
                ),
                Attrs::empty(),
            );
            assert_eq!(render_oper_member(&oper), expected);
        }
    }
}
