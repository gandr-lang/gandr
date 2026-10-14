//! The presentation code: `Sig`, the datatype whose values are presentations.
//!
//! A `sign` block presents a theory — sorts with their index telescopes,
//! operations with their input and output ports, rules as two terms over
//! variables — and [`sig_desc`] describes the datatype `Sig` whose values are
//! those presentations, in the first-order fragment every declared datatype is
//! described in. [`SigValue`] is one value of it: [`SigValue::encode`] builds
//! it from a presentation's [`SigParts`], [`SigValue::decode`] reads them back
//! and refuses a value the grammar does not admit, and [`SigValue::identity`]
//! is the value's canonical encoding under [`serialize_value`]. Those bytes are
//! the presentation's one identity: two presentations are the same exactly
//! when their values encode alike, and no serial, name or digest stands beside
//! them as a second one.
//!
//! # One sort, chained
//!
//! `Sig` is one self-recursive sort of eleven constructors, in tag order:
//!
//! | tag | constructor | fields |
//! |---|---|---|
//! | 0 | `Presents` | the sort chain, the operation chain, the rule chain |
//! | 1 | `End` | none: the end of every chain |
//! | 2 | `Sort` | name, its index ports, the rest of the sorts |
//! | 3 | `Oper` | name, its input ports, its output ports, the rest |
//! | 4 | `Port` | name, its sort's name, the sort's index arguments, the rest |
//! | 5 | `Rule` | name, its left term, its right term, the rest of the rules |
//! | 6 | `Var` | a variable's name |
//! | 7 | `App` | an operation's name, its arguments |
//! | 8 | `Con` | a constructor's name, its arguments |
//! | 9 | `Tuple` | the components of a results tuple |
//! | 10 | `Arg` | a term, the rest of the arguments |
//!
//! Every list a presentation holds is a chain of its member constructor ended
//! by `End`, and every name is a `String` field; an unnamed port carries the
//! empty name, so where a port was written leaves its value unchanged.
//!
//! - **Alternatives.** A family per syntactic class — sorts, operations, ports,
//!   terms — each list a `List` of its members, states the grammar in the
//!   types; it needs a field that applies a family to the family being declared
//!   and families that mention one another, both of which the native data
//!   reading refuses today. An inline sum per field (`Code::sum`) types the
//!   chains but leaves `case` no constructor names to match.
//! - **Reversal.** Nested occurrences and mutual families entering the native
//!   reading split `Sig` into its typed families; the identity bytes change
//!   with the constructor table, so the split is a change of every
//!   presentation's identity.
//!
//! # What waits
//!
//! The constructors above are the part of the code grammar the fragment
//! admits: sorts and their index telescopes, operations and their ports, and
//! rule faces between terms of variables, operation applications, constructor
//! applications and results tuples. The rest of the grammar waits on a
//! constructor `Sig` does not have yet: circuit rules (a body of wired nodes
//! and its rewrite ports), higher cells (a rule between rules), a sort's
//! polarity (every presented sort is data), constructors and parameters (a
//! presentation declares none), attributes, and atom binders. A presentation's
//! circuit rules are kept beside its value by the reader that reads them.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::ConstructorTag;
use crate::boundary::NominalSerial;
use crate::boundary::SerializedValueBytes;
use crate::code::Attrs;
use crate::code::Code;
use crate::code::Name;
use crate::code::PrimTy;
use crate::code::ValueTypeRef;
use crate::desc::CtorDesc;
use crate::desc::DeclPolarity;
use crate::desc::NominalId;
use crate::desc::SignDesc;
use crate::desc::SortDesc;
use crate::generic::DescValue;
use crate::generic::Payload;
use crate::generic::PayloadNode;
use crate::generic::PayloadView;
use crate::generic::serialize_value;
use crate::rule::FreeTerm;
use crate::rule::TermNode;
use crate::rule::TermView;

/// The names of `Sig`'s constructors, in tag order: the names a program that
/// matches on a presentation writes.
pub const SIG_CONSTRUCTORS: [&str; 11] = [
    "Presents", "End", "Sort", "Oper", "Port", "Rule", "Var", "App", "Con", "Tuple", "Arg",
];

/// Each constructor of `Sig`, in tag order, with its count of `String`
/// fields, which come first, and its count of recursive fields after them.
const CONSTRUCTORS: [(&str, usize, usize); 11] = [
    (SIG_CONSTRUCTORS[0], 0, 3),
    (SIG_CONSTRUCTORS[1], 0, 0),
    (SIG_CONSTRUCTORS[2], 1, 2),
    (SIG_CONSTRUCTORS[3], 1, 3),
    (SIG_CONSTRUCTORS[4], 2, 2),
    (SIG_CONSTRUCTORS[5], 1, 3),
    (SIG_CONSTRUCTORS[6], 1, 0),
    (SIG_CONSTRUCTORS[7], 1, 1),
    (SIG_CONSTRUCTORS[8], 1, 1),
    (SIG_CONSTRUCTORS[9], 0, 1),
    (SIG_CONSTRUCTORS[10], 0, 2),
];

/// One constructor of `Sig`, by its tag.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Tag
{
    /// The presentation: its sort, operation and rule chains.
    Presents,
    /// The end of a chain.
    End,
    /// A sort and the rest of the sorts.
    Sort,
    /// An operation and the rest of the operations.
    Oper,
    /// A port and the rest of the ports.
    Port,
    /// A rule face and the rest of the rules.
    Rule,
    /// A variable.
    Var,
    /// An operation application.
    App,
    /// A constructor application.
    Con,
    /// A results tuple.
    Tuple,
    /// An argument and the rest of the arguments.
    Arg,
}

impl Tag
{
    /// The constructor tag a value of this constructor carries: its position
    /// in the constructor table.
    ///
    /// # Specification
    /// trivial.
    fn constructor(self) -> ConstructorTag
    {
        ConstructorTag::from(match self {
            | Self::Presents => 0_usize,
            | Self::End => 1,
            | Self::Sort => 2,
            | Self::Oper => 3,
            | Self::Port => 4,
            | Self::Rule => 5,
            | Self::Var => 6,
            | Self::App => 7,
            | Self::Con => 8,
            | Self::Tuple => 9,
            | Self::Arg => 10,
        })
    }
}

/// The description of `Sig`, one data sort of eleven constructors.
///
/// The constructors stand in the order the module documentation tables; every
/// name is a `String` field and every other field a recursive occurrence.
///
/// # Specification
/// - ensures: no parameters, one data sort `Sig`, and the constructors
///   `Presents`, `End`, `Sort`, `Oper`, `Port`, `Rule`, `Var`, `App`, `Con`,
///   `Tuple` and `Arg` in that order, each at the result sort `Sig`; a
///   constructor's `String` fields carry `grade` and come first, `Port`'s two
///   and one for every other constructor that names something, and its
///   remaining fields are `Sig`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the constructor names, their field counts and the
///   string-then-recursion field order are observed through the decoded
///   constructor table and the exact identity bytes of a presentation;
///   reordered constructors, a dropped field or a name read as a recursion
///   change them.
/// - witness: `sig::tests::the_code_is_one_data_sort_of_eleven_constructors`
/// - witness: `sig::tests::a_presentation_encodes_to_its_exact_identity_bytes`
#[inline]
#[must_use]
#[spec(ensures: |ref desc| desc.id.name.as_ref() == "Sig"
    && desc.params.is_empty()
    && desc.sorts.iter().map(|sort| sort.name.as_ref()).eq(["Sig"])
    && desc.ctors.iter().map(|ctor| ctor.name.as_ref()).eq(CONSTRUCTORS.iter().map(|&(name, _, _)| name))
    && desc.ctors.iter().all(|ctor| ctor.result.as_ref() == "Sig"))]
pub fn sig_desc<G>(grade: G) -> SignDesc<G>
where
    G: Clone,
{
    let ctors: Vec<CtorDesc<G>> = CONSTRUCTORS
        .iter()
        .map(|&(name, strings, recursions)| {
            let mut codes: Vec<Code<G>> = Vec::with_capacity(strings.saturating_add(recursions));
            for _ in 0 .. strings {
                codes.push(Code::field(
                    ValueTypeRef::prim(PrimTy::StringTy),
                    grade.clone(),
                    Attrs::empty(),
                ));
            }
            for _ in 0 .. recursions {
                codes.push(Code::var("Sig"));
            }
            let mut code = codes.pop().unwrap_or_else(Code::unit);
            while let Some(left) = codes.pop() {
                code = Code::prod(left, code);
            }
            CtorDesc::new(name, code, "Sig", Attrs::empty())
        })
        .collect();
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Sig"),
        [],
        ctors,
        [],
        [],
        DeclPolarity::Data,
        Attrs::empty(),
    )
    .with_sorts([SortDesc::new("Sig", DeclPolarity::Data)])
}

/// One port of a presentation: its name, empty when it was written unnamed,
/// and its sort, a sort name over index terms.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the index terms keep their written order.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::encode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SigPort
{
    /// The port's name; empty for an unnamed port.
    pub name: Name,
    /// The name of the port's sort.
    pub sort: Name,
    /// The sort's index terms, in order.
    pub indices: Vec<FreeTerm>,
}

/// One sort of a presentation: its name and its index telescope.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the index ports keep their written order; each binds its name in
///   the ones after it.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::encode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SigSort
{
    /// The sort's name.
    pub name: Name,
    /// The index telescope, in order.
    pub indices: Vec<SigPort>,
}

/// One operation of a presentation: its name and its two port lists.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: both port lists keep their written order.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::encode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SigOperation
{
    /// The operation's name.
    pub name: Name,
    /// The input ports, in order.
    pub inputs: Vec<SigPort>,
    /// The output ports, in order.
    pub outputs: Vec<SigPort>,
}

/// One rule face of a presentation: its name and its two terms.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the sides keep their written orientation, left to right.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::encode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SigRule
{
    /// The rule's name.
    pub name: Name,
    /// The left-hand side.
    pub left: FreeTerm,
    /// The right-hand side.
    pub right: FreeTerm,
}

/// A presentation's members as `Sig` codes them, each list in written order.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each list keeps its members' written order.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::encode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct SigParts
{
    /// The sorts.
    pub sorts: Vec<SigSort>,
    /// The operations.
    pub operations: Vec<SigOperation>,
    /// The rule faces.
    pub rules: Vec<SigRule>,
}

/// Why a value of `Sig`'s description codes no presentation.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each variant names the first place the value departs from the
///   grammar, read root first.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SigFault
{
    /// A constructor stands where the grammar admits another: the root is not
    /// `Presents`, a chain holds a foreign member, or a term position holds no
    /// term.
    Misplaced(ConstructorTag),
    /// A payload's shape is not its constructor's code.
    Payload,
    /// A name is not UTF-8 text.
    Text,
}

/// A value of `Sig`: one presentation.
///
/// # Specification
/// - requires: nothing to construct this data through [`Self::encode`];
///   [`Self::from_value`] admits any value, which [`Self::decode`] judges.
/// - ensures: the value is a value of [`sig_desc`]'s description.
/// - executable: none — a data carrier; its operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Self::encode`] and [`Self::decode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SigValue(DescValue);

impl SigValue
{
    /// The value coding `parts`.
    ///
    /// # Specification
    /// - ensures: the root is `Presents` over the sort, operation and rule
    ///   chains, each member in order; [`Self::decode`] reads `parts` back.
    /// - panics: none.
    /// - intension: every chain is folded from its end and every term built
    ///   from a post-order worklist, so no step recurses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation with an indexed sort, a two-output
    ///   operation, an unnamed port and rules whose sides apply operations,
    ///   constructors and a results tuple round-trips exactly and encodes to
    ///   its exact bytes; a dropped member, a swapped chain or a lost index
    ///   changes the decoded parts or the bytes.
    /// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
    /// - witness: `sig::tests::a_presentation_encodes_to_its_exact_identity_bytes`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref value| value.0.ctor == Tag::Presents.constructor())]
    pub fn encode(parts: &SigParts) -> Self
    {
        let mut sorts = value(Tag::End, Vec::new());
        for sort in parts.sorts.iter().rev() {
            let indices = ports(&sort.indices);
            sorts = value(Tag::Sort, vec![leaf(&sort.name), rec(indices), rec(sorts)]);
        }
        let mut operations = value(Tag::End, Vec::new());
        for operation in parts.operations.iter().rev() {
            let inputs = ports(&operation.inputs);
            let outputs = ports(&operation.outputs);
            operations = value(Tag::Oper, vec![
                leaf(&operation.name),
                rec(inputs),
                rec(outputs),
                rec(operations),
            ]);
        }
        let mut rules = value(Tag::End, Vec::new());
        for rule in parts.rules.iter().rev() {
            let left = term(rule.left.to_node());
            let right = term(rule.right.to_node());
            rules = value(Tag::Rule, vec![
                leaf(&rule.name),
                rec(left),
                rec(right),
                rec(rules),
            ]);
        }
        Self(value(Tag::Presents, vec![
            rec(sorts),
            rec(operations),
            rec(rules),
        ]))
    }

    /// A value of `Sig`'s description, whatever it codes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn from_value(value: DescValue) -> Self
    {
        Self(value)
    }

    /// The generic value this presentation is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn as_value(&self) -> &DescValue
    {
        &self.0
    }

    /// The presentation the value codes.
    ///
    /// # Specification
    /// - ensures: the parts [`Self::encode`] was given, for a value it built; a
    ///   value read is a `Presents` value.
    /// - fails: a root other than `Presents`, a chain member of another
    ///   constructor, a term position holding no term, a payload unlike its
    ///   constructor's code, or a name that is not UTF-8.
    /// - panics: none.
    /// - intension: chains are walked in loops and terms rebuilt from a
    ///   post-order worklist, so no step recurses.
    ///
    /// # Errors
    /// Returns the first [`SigFault`] met, root first.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the round trip of a presentation exercising every
    ///   constructor, and four malformed values — an `End` root, a rule in the
    ///   sort chain, a port where a term stands, a non-UTF-8 name — each
    ///   refused by its exact fault.
    /// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
    /// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
    #[inline]
    #[spec(ensures: |ref ret| ret.is_err() || self.0.ctor == Tag::Presents.constructor())]
    pub fn decode(&self) -> Result<SigParts, SigFault>
    {
        let root = Node {
            ctor: self.0.ctor,
            payload: self.0.payload.to_node(),
        };
        let [sorts, operations, rules] = expect::<3>(root, Tag::Presents)?;
        let mut parts = SigParts::default();
        let mut at = nested(sorts)?;
        loop {
            let next = member::<3>(at, Tag::Sort)?;
            let Maybe::Present([name, indices, rest]) = next
            else {
                break;
            };
            let name = text(name)?;
            let indices = nested(indices)?;
            let indices = read_ports(indices)?;
            parts.sorts.push(SigSort { name, indices });
            at = nested(rest)?;
        }
        let mut at = nested(operations)?;
        loop {
            let next = member::<4>(at, Tag::Oper)?;
            let Maybe::Present([name, inputs, outputs, rest]) = next
            else {
                break;
            };
            let name = text(name)?;
            let inputs = nested(inputs)?;
            let inputs = read_ports(inputs)?;
            let outputs = nested(outputs)?;
            let outputs = read_ports(outputs)?;
            parts.operations.push(SigOperation {
                name,
                inputs,
                outputs,
            });
            at = nested(rest)?;
        }
        let mut at = nested(rules)?;
        loop {
            let next = member::<4>(at, Tag::Rule)?;
            let Maybe::Present([name, left, right, rest]) = next
            else {
                break;
            };
            let name = text(name)?;
            let left = nested(left)?;
            let left = read_term(left)?;
            let right = nested(right)?;
            let right = read_term(right)?;
            parts.rules.push(SigRule { name, left, right });
            at = nested(rest)?;
        }
        Ok(parts)
    }

    /// The value's canonical bytes: the presentation's identity.
    ///
    /// # Specification
    /// - ensures: [`serialize_value`] of the value under [`sig_desc`]'s
    ///   description; two values encode alike exactly when they are equal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation's exact bytes pin tag order, field
    ///   order and name lengths; two presentations differing in one port name
    ///   encode apart, and the same presentation read twice encodes alike.
    /// - witness: `sig::tests::a_presentation_encodes_to_its_exact_identity_bytes`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref bytes| *bytes == serialize_value(&sig_desc(()), &self.0))]
    pub fn identity(&self) -> SerializedValueBytes
    {
        serialize_value(&sig_desc(()), &self.0)
    }
}

/// A value of the constructor `tag` over `fields`, in order.
///
/// # Specification
/// trivial.
fn value(
    tag: Tag,
    mut fields: Vec<Payload>,
) -> DescValue
{
    let mut payload = fields.pop().unwrap_or_else(Payload::unit);
    while let Some(left) = fields.pop() {
        payload = Payload::pair(left, payload);
    }
    DescValue::new(tag.constructor(), payload)
}

/// A name field.
///
/// # Specification
/// trivial.
fn leaf(name: &Name) -> Payload
{
    Payload::leaf(name.as_ref().as_bytes())
}

/// A recursive field.
///
/// # Specification
/// trivial.
fn rec(nested: DescValue) -> Payload
{
    Payload::rec(nested)
}

/// The chain coding `list`, in order.
///
/// # Specification
/// trivial.
fn ports(list: &[SigPort]) -> DescValue
{
    let mut chain = value(Tag::End, Vec::new());
    for port in list.iter().rev() {
        let indices = arguments(
            port.indices
                .iter()
                .map(|index| term(index.to_node()))
                .collect(),
        );
        chain = value(Tag::Port, vec![
            leaf(&port.name),
            leaf(&port.sort),
            rec(indices),
            rec(chain),
        ]);
    }
    chain
}

/// The argument chain over `terms`, in order.
///
/// # Specification
/// trivial.
fn arguments(terms: Vec<DescValue>) -> DescValue
{
    let mut chain = value(Tag::End, Vec::new());
    for argument in terms.into_iter().rev() {
        chain = value(Tag::Arg, vec![rec(argument), rec(chain)]);
    }
    chain
}

/// One pending step of [`term`].
enum Build<'term>
{
    /// Code this term node.
    Visit(TermNode<'term>),
    /// Apply the head to the last `count` coded terms.
    Apply(Tag, Maybe<&'term Name, applied::Absent>, usize),
}

quenchant_shape::reason_enum! {
    /// Why an application step carries no head name.
    mod applied {
        /// The reason the step names no head.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// A results tuple has components and no head.
            Tuple,
        }
    }
}

/// The value coding the free term at `root`.
///
/// # Specification
/// - ensures: a variable is `Var`, an operation application `App`, a
///   constructor application `Con` and a results tuple `Tuple`, each
///   application over the argument chain of its arguments in order.
/// - panics: none.
/// - executable: none — the coding is observed by reading it back, which the
///   round trip of [`SigValue::decode`] does.
/// - intension: a post-order worklist with a stack of coded terms.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::encode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
fn term(root: TermNode<'_>) -> DescValue
{
    let mut pending = vec![Build::Visit(root)];
    let mut built: Vec<DescValue> = Vec::new();
    while let Some(step) = pending.pop() {
        match step {
            | Build::Visit(node) => {
                let (tag, head, args) = match node.view() {
                    | TermView::Var(name) => {
                        built.push(value(Tag::Var, vec![leaf(name)]));
                        continue;
                    },
                    | TermView::Op { name, args } => (Tag::App, Maybe::Present(name), args),
                    | TermView::Ctor { name, args } => (Tag::Con, Maybe::Present(name), args),
                    | TermView::Results { args } => {
                        (Tag::Tuple, Maybe::Absent(applied::Absent::Tuple), args)
                    },
                };
                pending.push(Build::Apply(tag, head, args.len()));
                let first = pending.len();
                pending.extend(args.map(Build::Visit));
                if let Some(children) = pending.get_mut(first ..) {
                    children.reverse();
                }
            },
            | Build::Apply(tag, head, count) => {
                let start = built.len().saturating_sub(count);
                let chain = arguments(built.split_off(start));
                built.push(match head {
                    | Maybe::Present(name) => value(tag, vec![leaf(name), rec(chain)]),
                    | Maybe::Absent(_) => value(tag, vec![rec(chain)]),
                });
            },
        }
    }
    built.pop().unwrap_or_else(|| value(Tag::End, Vec::new()))
}

/// A nested value: its constructor tag and its payload.
#[derive(Clone, Copy, Debug)]
struct Node<'value>
{
    /// The constructor tag.
    ctor: ConstructorTag,
    /// The payload under it.
    payload: PayloadNode<'value>,
}

/// The fields of `node`, which must be a `tag` value.
///
/// # Specification
/// - ensures: the `N` fields of the right-nested product, left to right.
/// - fails: [`SigFault::Misplaced`] for another constructor;
///   [`SigFault::Payload`] for a payload of another shape.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| ret.is_err() || node.ctor == tag.constructor())]
fn expect<const N: usize>(
    node: Node<'_>,
    tag: Tag,
) -> Result<[PayloadNode<'_>; N], SigFault>
{
    if node.ctor != tag.constructor() {
        return Err(SigFault::Misplaced(node.ctor));
    }
    let mut fields = Vec::with_capacity(N);
    let mut rest = node.payload;
    for _ in 1 .. N {
        let PayloadView::Pair(mut halves) = rest.view()
        else {
            return Err(SigFault::Payload);
        };
        let (Some(left), Some(right)) = (halves.next(), halves.next())
        else {
            return Err(SigFault::Payload);
        };
        fields.push(left);
        rest = right;
    }
    if N > 0 {
        fields.push(rest);
    }
    <[PayloadNode<'_>; N]>::try_from(fields).map_err(|_unequal| SigFault::Payload)
}

quenchant_shape::reason_enum! {
    /// Why a chain yields no further member.
    mod chained {
        /// The reason the chain stops.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The chain reached its `End`.
            Ended,
        }
    }
}

/// The next member of a chain of `tag` members at `node`.
///
/// # Specification
/// - ensures: the member's fields when `node` is a `tag` value, the ended
///   absence when it is `End`.
/// - fails: as [`expect`] for any other constructor or payload.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Absent(_)) => node.ctor == Tag::End.constructor(),
    | Ok(Maybe::Present(_)) => node.ctor == tag.constructor(),
    | Err(_) => true,
})]
fn member<const N: usize>(
    node: Node<'_>,
    tag: Tag,
) -> Result<Maybe<[PayloadNode<'_>; N], chained::Absent>, SigFault>
{
    if node.ctor == Tag::End.constructor() {
        let [] = expect::<0>(node, Tag::End)?;
        if !matches!(node.payload.view(), PayloadView::Unit) {
            return Err(SigFault::Payload);
        }
        return Ok(Maybe::Absent(chained::Absent::Ended));
    }
    let fields = expect::<N>(node, tag)?;
    Ok(Maybe::Present(fields))
}

/// The value a recursive field holds.
///
/// # Specification
/// - ensures: the nested value's tag and payload.
/// - fails: [`SigFault::Payload`] for a field that is no recursive occurrence.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| ret.is_ok() == matches!(field.view(), PayloadView::Rec { .. }))]
fn nested(field: PayloadNode<'_>) -> Result<Node<'_>, SigFault>
{
    let PayloadView::Rec {
        ctor,
        payload: mut inner,
    } = field.view()
    else {
        return Err(SigFault::Payload);
    };
    let payload = inner.next().ok_or(SigFault::Payload)?;
    Ok(Node { ctor, payload })
}

/// The name a `String` field holds.
///
/// # Specification
/// - ensures: the field's bytes as a name.
/// - fails: [`SigFault::Payload`] for a field that is no leaf;
///   [`SigFault::Text`] for bytes that are not UTF-8.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| ret.is_ok() == matches!(
    field.view(),
    PayloadView::Leaf(bytes) if core::str::from_utf8(bytes.as_ref()).is_ok()
))]
fn text(field: PayloadNode<'_>) -> Result<Name, SigFault>
{
    let PayloadView::Leaf(bytes) = field.view()
    else {
        return Err(SigFault::Payload);
    };
    let spelled = core::str::from_utf8(bytes.as_ref()).map_err(|_invalid| SigFault::Text)?;
    Ok(Name::from(spelled))
}

/// The ports of the chain at `node`, in order.
///
/// # Specification
/// - ensures: one port per `Port` member, each with its index terms.
/// - fails: as [`member`], [`text`] and [`read_term`].
/// - panics: none.
/// - executable: none — a predicate would read the chain a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
fn read_ports(mut node: Node<'_>) -> Result<Vec<SigPort>, SigFault>
{
    let mut ports = Vec::new();
    loop {
        let next = member::<4>(node, Tag::Port)?;
        let Maybe::Present([name, sort, indices, rest]) = next
        else {
            break;
        };
        let name = text(name)?;
        let sort = text(sort)?;
        let indices = nested(indices)?;
        let indices = read_arguments(indices)?;
        ports.push(SigPort {
            name,
            sort,
            indices,
        });
        node = nested(rest)?;
    }
    Ok(ports)
}

/// The terms of the argument chain at `node`, in order.
///
/// # Specification
/// - ensures: one term per `Arg` member.
/// - fails: as [`member`] and [`read_term`].
/// - panics: none.
/// - executable: none — a predicate would read the chain a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
fn read_arguments(node: Node<'_>) -> Result<Vec<FreeTerm>, SigFault>
{
    let arguments = argument_nodes(node)?;
    let mut terms = Vec::with_capacity(arguments.len());
    for argument in arguments {
        let term = read_term(argument)?;
        terms.push(term);
    }
    Ok(terms)
}

/// The nodes of the argument chain at `node`, in order.
///
/// # Specification
/// - ensures: the term of each `Arg` member.
/// - fails: as [`member`].
/// - panics: none.
/// - executable: none — a predicate would read the chain a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
fn argument_nodes(mut node: Node<'_>) -> Result<Vec<Node<'_>>, SigFault>
{
    let mut nodes = Vec::new();
    loop {
        let next = member::<2>(node, Tag::Arg)?;
        let Maybe::Present([argument, rest]) = next
        else {
            break;
        };
        let argument = nested(argument)?;
        nodes.push(argument);
        node = nested(rest)?;
    }
    Ok(nodes)
}

/// The head a term application read back carries.
enum Applied
{
    /// An operation application, by the operation's name.
    Operation(Name),
    /// A constructor application, by the constructor's name.
    Constructor(Name),
    /// A results tuple.
    Tuple,
}

/// One pending step of [`read_term`].
enum Read<'value>
{
    /// Read this node as a term.
    Visit(Node<'value>),
    /// Apply the head to the last `count` read terms.
    Apply(Applied, usize),
}

/// The free term the value at `root` codes.
///
/// # Specification
/// - ensures: the inverse of [`term`]: `Var`, `App`, `Con` and `Tuple` read
///   back to a variable, an operation application, a constructor application
///   and a results tuple.
/// - fails: [`SigFault::Misplaced`] for any other constructor; as [`expect`],
///   [`text`] and [`argument_nodes`] beneath.
/// - panics: none.
/// - executable: none — the reading is observed by coding it again, which the
///   round trip of [`SigValue::decode`] does.
/// - intension: a post-order worklist with a stack of read terms.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SigValue::decode`].
/// - witness: `sig::tests::a_presentation_round_trips_through_its_value`
/// - witness: `sig::tests::a_value_outside_the_grammar_is_refused_by_name`
fn read_term(root: Node<'_>) -> Result<FreeTerm, SigFault>
{
    let mut pending = vec![Read::Visit(root)];
    let mut read: Vec<FreeTerm> = Vec::new();
    while let Some(step) = pending.pop() {
        match step {
            | Read::Visit(node) => {
                let (applied, chain) = if node.ctor == Tag::Var.constructor() {
                    let [name] = expect::<1>(node, Tag::Var)?;
                    let name = text(name)?;
                    read.push(FreeTerm::var(name));
                    continue;
                }
                else if node.ctor == Tag::App.constructor() {
                    let [head, chain] = expect::<2>(node, Tag::App)?;
                    let head = text(head)?;
                    (Applied::Operation(head), chain)
                }
                else if node.ctor == Tag::Con.constructor() {
                    let [head, chain] = expect::<2>(node, Tag::Con)?;
                    let head = text(head)?;
                    (Applied::Constructor(head), chain)
                }
                else if node.ctor == Tag::Tuple.constructor() {
                    let [chain] = expect::<1>(node, Tag::Tuple)?;
                    (Applied::Tuple, chain)
                }
                else {
                    return Err(SigFault::Misplaced(node.ctor));
                };
                let chain = nested(chain)?;
                let arguments = argument_nodes(chain)?;
                pending.push(Read::Apply(applied, arguments.len()));
                pending.extend(arguments.into_iter().rev().map(Read::Visit));
            },
            | Read::Apply(applied, count) => {
                let start = read.len().saturating_sub(count);
                let arguments = read.split_off(start);
                read.push(match applied {
                    | Applied::Operation(head) => FreeTerm::op(head, arguments),
                    | Applied::Constructor(head) => FreeTerm::ctor(head, arguments),
                    | Applied::Tuple => FreeTerm::results(arguments),
                });
            },
        }
    }
    read.pop().ok_or(SigFault::Payload)
}

#[cfg(test)]
mod tests;
