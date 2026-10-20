//! The presentation code: `Theory`, the datatype whose values are
//! presentations.
//!
//! A `theory` block presents a theory — sorts with their index telescopes,
//! operations with their input and output ports, rules as two terms over
//! variables — and [`theory_desc`] describes the datatype `Theory` whose values
//! are those presentations, in the first-order fragment every declared datatype
//! is described in. [`TheoryValue`] is one value of it: [`TheoryValue::encode`]
//! builds it from a presentation's [`TheoryParts`], [`TheoryValue::decode`]
//! reads them back and refuses a value the grammar does not admit, and
//! [`TheoryValue::identity`] is the value's canonical encoding under
//! [`serialize_value`]. Those bytes are the presentation's one identity: two
//! presentations are the same exactly when their values encode alike, and no
//! serial, name or digest stands beside them as a second one.
//!
//! # The word
//!
//! The block presents a theory and `Theory` is the datatype of presentations,
//! so `theory Monoid { … }` binds `Monoid : Theory` and `Model(Monoid)` is the
//! signature of its models: the object theories of Kovács and Sattler's
//! generalised logical framework, presented by a signature in Kaposi and
//! Xie's sense, and the word Clear, OBJ and Maude chose for the same construct
//! (`th`, `fth`).
//!
//! - **Choice.** One word at both levels, the keyword and the datatype.
//! - **Alternatives.** `sign` and `Sig`, the earlier spelling, named the
//!   presentation rather than what it presents and spelled one concept two
//!   ways; `signature` is overloaded by ML's module types; a second keyword
//!   beside the first for a theory that organises rather than presents splits
//!   one construct along a line the operations on it (inclusion, extension)
//!   draw better.
//! - **Reversal.** A former whose values are not presentations would take a
//!   word of its own; the identity bytes carry constructor tags, never the
//!   datatype's name, so a rename moves no presentation's identity.
//!
//! # Two encodings of a `theory` block
//!
//! A `theory` block has two encodings, and the second is read off the first.
//! [`TheoryValue`] is the presentation as a value: what the block states, coded
//! so its bytes are the presentation's identity, the core definition `S :
//! Theory` and what `Model(S)` derives from. [`TheoryDesc`] is the declaration
//! table that [`check_desc`](crate::check_desc), the first-order fold
//! ([`first_order`](crate::first_order())) and the cell layer read; every
//! `data` declaration and retrofitted former shares it, so it also has fields
//! no presentation fills: parameters, constructors as graded and attributed
//! codes, a polarity. The `theory` reader encodes the value once and decodes
//! the table from it, adding three things the value cannot hold. The first is
//! the minted nominal identity: the value's identity is structural, so two
//! blocks that state the same members share one identity yet stay two
//! declarations. The second is the members' spans, which are provenance and
//! would tie identity to layout. The third is the circuit rules, which `Theory`
//! does not code yet (§ What waits) and which travel beside the value.
//!
//! - **Choice.** The table is a reading of the value, not a second record of
//!   the block: one reading of the block, one identity, and the consumers of
//!   the table unchanged.
//! - **Alternatives.** Reading the block twice, once into each encoding, lets
//!   the two drift. The value alone, with every consumer reading `Theory`,
//!   moves the cell layer onto a code that does not yet hold circuit rules.
//! - **Reversal.** Once `Theory` codes circuit rules, a `theory` block's table
//!   is wholly a reading of its value, and its consumers can read the value
//!   itself. The decoding lives in the `theory` reader today; moving it here,
//!   as the one function from a value, its nominal identity and its spans to a
//!   table, is the step before.
//!
//! # One sort, chained
//!
//! `Theory` is one self-recursive sort of sixteen constructors, in tag order:
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
//! | 11 | `Representable` | as `Sort`, for a representable sort |
//! | 12 | `Bound` | as `Port`, then its binders, before the rest |
//! | 13 | `Shape` | name, size, its face chain, the rest of the sorts |
//! | 14 | `Face` | name, its points, the rest of the faces |
//! | 15 | `Obs` | as `Oper`, for an observation |
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
//!   reading split `Theory` into its typed families; the identity bytes change
//!   with the constructor table, so the split is a change of every
//!   presentation's identity.
//!
//! # Second-order presentations
//!
//! A sort declared `Type+` is representable: it admits context extension, so
//! a port may bind a variable of it (Kaposi and Xie, _Second-Order Generalised
//! Algebraic Theories_, FSCD 2024, Definition 3). Such a sort is a
//! `Representable` member of the sort chain; a port written `t : pi+ (x : S) .
//! T` is a `Bound` member of its operation's port chain, its binders a chain of
//! plain `Port`s, outermost first. A binder binds nothing of its own, a sort's
//! index port binds nothing, and a `Bound` port binds at least one variable, so
//! the value of a port has one spelling.
//!
//! - **Choice.** Representability and binding are constructors of their own,
//!   appended to the table, rather than a field of every `Sort` and `Port`.
//!   Tags are positions, so a presentation that declares neither keeps the
//!   bytes it had, and a first-order presentation's identity is what it was
//!   before the second-order constructors existed. The alternative, a
//!   representability field on every sort and a binder chain on every port,
//!   states the grammar more uniformly but re-keys every presentation for a
//!   distinction none of them draws, and the field still needs two constructors
//!   of its own to code the bit.
//! - **Reversal.** The typed split above, which re-keys every presentation
//!   anyway, carries representability and binding as fields of its sort and
//!   port families.
//!
//! # The shape parameter
//!
//! A signature stated over a finite shape, `shape Square : 4 { left = {0, 2};
//! }`, codes it as a `Shape` member at the head of its sort chain: the shape's
//! name, its size as a decimal numeral, and the chain of its faces, each a
//! `Face` with its name and its points as decimal numerals joined by `,`,
//! ascending and each once. A sort chain holds at most one `Shape`, first; a
//! presentation that states none keeps the bytes it had, as a first-order one
//! does beside the second-order constructors.
//!
//! - **Choice.** A size and a point are numerals in a `String` field, as a name
//!   is: one constructor for the shape and one for a face, and a face's points
//!   one field in their one spelling, so a subshape has one value. The
//!   alternatives were a unary chain of point constructors under each face,
//!   which codes a number in constructors at the cost of a value per point of
//!   every face, and a membership string over the carrier, which cannot hold a
//!   point outside it — and the description check must see such a point to
//!   refuse it by name.
//! - **Reversal.** A program over `Theory` that computes with a shape's points,
//!   rather than carrying them, wants a numeric field the code grammar does not
//!   have yet; that field replaces the numerals and re-keys every shaped
//!   presentation.
//!
//! # Observations
//!
//! An `obs` member declares an observation of a sort: the coalgebraic dual of
//! an operation, written with the same two port lists. It is an `Obs` member
//! of the operation chain, in written order among the operations, with
//! `Oper`'s fields. The constructor is appended to the table, so a
//! presentation that declares no observation keeps the bytes it had.
//!
//! # Inclusion
//!
//! [`TheoryParts::include`] is `include` on presentations: it extends a
//! presentation by another's members, the included members first, and
//! returns the inclusion as a [`TheoryInclusion`], the position of each
//! included member among the extended presentation's. A member already
//! present under its name is the same member, so two included presentations
//! that share a sub-presentation meet along it: the extension is their
//! pushout over the members they share. A member present under its name with
//! another definition is an [`IncludeClash`]. [`TheoryParts::restrict`] reads
//! a presentation back along an inclusion, and the inclusion is a morphism
//! exactly because restricting the extension along it gives back the
//! included presentation.
//!
//! # What waits
//!
//! The constructors above are the part of the code grammar the fragment
//! admits: a shape parameter and its faces, sorts and their index telescopes,
//! representable sorts, operations and their ports, ports under restricted
//! binders, and rule faces between terms of variables, operation
//! applications, constructor applications and results tuples. The rest of
//! the grammar waits on a constructor `Theory` does not have yet: circuit rules
//! (a body of wired nodes and its rewrite ports), higher cells (a rule between
//! rules), a sort's polarity (every presented sort is data), constructors and
//! parameters (a presentation declares none), attributes, and atom binders. A
//! presentation's circuit rules are kept beside its value by the reader that
//! reads them.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::ConstructorTag;
use crate::boundary::NominalSerial;
use crate::boundary::SerializedValueBytes;
use crate::boundary::ShapePoint;
use crate::boundary::ShapeSize;
use crate::code::Attrs;
use crate::code::Code;
use crate::code::Name;
use crate::code::PrimTy;
use crate::code::ValueTypeRef;
use crate::desc::CtorDesc;
use crate::desc::DeclPolarity;
use crate::desc::NominalId;
use crate::desc::Representability;
use crate::desc::ShapeFace;
use crate::desc::SortDesc;
use crate::desc::TheoryDesc;
use crate::desc::TheoryShape;
use crate::desc::shape_parameter;
use crate::generic::DescValue;
use crate::generic::Payload;
use crate::generic::PayloadNode;
use crate::generic::PayloadView;
use crate::generic::serialize_value;
use crate::rule::FreeTerm;
use crate::rule::TermNode;
use crate::rule::TermView;

/// The names of `Theory`'s constructors, in tag order: the names a program that
/// matches on a presentation writes.
pub const THEORY_CONSTRUCTORS: [&str; 16] = [
    "Presents",
    "End",
    "Sort",
    "Oper",
    "Port",
    "Rule",
    "Var",
    "App",
    "Con",
    "Tuple",
    "Arg",
    "Representable",
    "Bound",
    "Shape",
    "Face",
    "Obs",
];

/// Each constructor of `Theory`, in tag order, with its count of `String`
/// fields, which come first, and its count of recursive fields after them.
const CONSTRUCTORS: [(&str, usize, usize); 16] = [
    (THEORY_CONSTRUCTORS[0], 0, 3),
    (THEORY_CONSTRUCTORS[1], 0, 0),
    (THEORY_CONSTRUCTORS[2], 1, 2),
    (THEORY_CONSTRUCTORS[3], 1, 3),
    (THEORY_CONSTRUCTORS[4], 2, 2),
    (THEORY_CONSTRUCTORS[5], 1, 3),
    (THEORY_CONSTRUCTORS[6], 1, 0),
    (THEORY_CONSTRUCTORS[7], 1, 1),
    (THEORY_CONSTRUCTORS[8], 1, 1),
    (THEORY_CONSTRUCTORS[9], 0, 1),
    (THEORY_CONSTRUCTORS[10], 0, 2),
    (THEORY_CONSTRUCTORS[11], 1, 2),
    (THEORY_CONSTRUCTORS[12], 2, 3),
    (THEORY_CONSTRUCTORS[13], 2, 2),
    (THEORY_CONSTRUCTORS[14], 2, 1),
    (THEORY_CONSTRUCTORS[15], 1, 3),
];

/// One constructor of `Theory`, by its tag.
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
    /// A representable sort and the rest of the sorts.
    Representable,
    /// A port under its binders and the rest of the ports.
    Bound,
    /// The shape parameter, its faces and the rest of the sorts.
    Shape,
    /// A face of the shape and the rest of the faces.
    Face,
    /// An observation and the rest of the operations.
    Obs,
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
            Self::Presents => 0_usize,
            Self::End => 1,
            Self::Sort => 2,
            Self::Oper => 3,
            Self::Port => 4,
            Self::Rule => 5,
            Self::Var => 6,
            Self::App => 7,
            Self::Con => 8,
            Self::Tuple => 9,
            Self::Arg => 10,
            Self::Representable => 11,
            Self::Bound => 12,
            Self::Shape => 13,
            Self::Face => 14,
            Self::Obs => 15,
        })
    }
}

/// The description of `Theory`, one data sort of sixteen constructors.
///
/// The constructors stand in the order the module documentation tables; every
/// name is a `String` field and every other field a recursive occurrence.
///
/// # Specification
/// - ensures: no parameters, one data sort `Theory`, and the constructors
///   `Presents`, `End`, `Sort`, `Oper`, `Port`, `Rule`, `Var`, `App`, `Con`,
///   `Tuple`, `Arg`, `Representable`, `Bound`, `Shape`, `Face` and `Obs` in
///   that order, each at the result sort `Theory`; a constructor's `String`
///   fields carry `grade` and come first, two for `Port`, `Bound`, `Shape` and
///   `Face` and one for every other constructor that names something, and its
///   remaining fields are `Theory`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the constructor names, their field counts and the
///   string-then-recursion field order are observed through the decoded
///   constructor table and the exact identity bytes of a presentation;
///   reordered constructors, a dropped field or a name read as a recursion
///   change them.
/// - witness: `theory::tests::the_code_is_one_data_sort_of_sixteen_constructors`
/// - witness: `theory::tests::a_presentation_encodes_to_its_exact_identity_bytes`
#[inline]
#[must_use]
#[spec(ensures: |ref desc| desc.id.name.as_ref() == "Theory"
    && desc.params.is_empty()
    && desc.sorts.iter().map(|sort| sort.name.as_ref()).eq(["Theory"])
    && desc.ctors.iter().map(|ctor| ctor.name.as_ref()).eq(CONSTRUCTORS.iter().map(|&(name, _, _)| name))
    && desc.ctors.iter().all(|ctor| ctor.result.as_ref() == "Theory"))]
pub fn theory_desc<G>(grade: G) -> TheoryDesc<G>
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
                codes.push(Code::var("Theory"));
            }
            let mut code = codes.pop().unwrap_or_else(Code::unit);
            while let Some(left) = codes.pop() {
                code = Code::prod(left, code);
            }
            CtorDesc::new(name, code, "Theory", Attrs::empty())
        })
        .collect();
    TheoryDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Theory"),
        [],
        ctors,
        [],
        [],
        DeclPolarity::Data,
        Attrs::empty(),
    )
    .with_sorts([SortDesc::new("Theory", DeclPolarity::Data)])
}

/// One port of a presentation: its name, empty when it was written unnamed,
/// its sort, a sort name over index terms, and the variables it binds.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the index terms and the binders keep their written order, the
///   outermost binder first.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::encode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryPort
{
    /// The port's name; empty for an unnamed port.
    pub name: Name,
    /// The name of the port's sort.
    pub sort: Name,
    /// The sort's index terms, in order.
    pub indices: Vec<FreeTerm>,
    /// The `pi+` binders over the port, outermost first, each a variable of a
    /// representable sort; empty for a first-order port. Only an operation's
    /// port binds.
    pub bindings: Vec<TheoryBinder>,
}

/// One `pi+` binder of a port: the bound variable's name and its sort, a
/// representable sort name over index terms. A binder binds nothing of its
/// own.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the index terms keep their written order.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::encode`].
/// - witness: `theory::tests::a_second_order_presentation_encodes_its_binders`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryBinder
{
    /// The bound variable's name.
    pub name: Name,
    /// The name of the variable's sort.
    pub sort: Name,
    /// The sort's index terms, in order.
    pub indices: Vec<FreeTerm>,
}

/// One sort of a presentation: its name, its index telescope and whether it
/// is representable.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the index ports keep their written order; each binds its name in
///   the ones after it.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::encode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheorySort
{
    /// The sort's name.
    pub name: Name,
    /// The index telescope, in order.
    pub indices: Vec<TheoryPort>,
    /// Whether a port may bind a variable of the sort.
    pub representability: Representability,
}

/// One operation of a presentation: its name, its kind and its two port
/// lists.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: both port lists keep their written order.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::encode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryOperation
{
    /// The operation's name.
    pub name: Name,
    /// Whether it is an operation or an observation.
    pub kind: OperationKind,
    /// The input ports, in order.
    pub inputs: Vec<TheoryPort>,
    /// The output ports, in order.
    pub outputs: Vec<TheoryPort>,
}

/// Which member declared an operation of a presentation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperationKind
{
    /// An `oper` member: a generator that builds its outputs.
    Operation,
    /// An `obs` member: an observation of its input's sort.
    Observation,
}

/// One rule face of a presentation: its name and its two terms.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the sides keep their written orientation, left to right.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::encode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryRule
{
    /// The rule's name.
    pub name: Name,
    /// The left-hand side.
    pub left: FreeTerm,
    /// The right-hand side.
    pub right: FreeTerm,
}

/// A presentation's members as `Theory` codes them, each list in written order.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each list keeps its members' written order.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::encode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryParts
{
    /// The shape parameter, absent for a presentation that states none.
    pub shape: Maybe<TheoryShape, shape_parameter::Absent>,
    /// The sorts.
    pub sorts: Vec<TheorySort>,
    /// The operations.
    pub operations: Vec<TheoryOperation>,
    /// The rule faces.
    pub rules: Vec<TheoryRule>,
}

impl Default for TheoryParts
{
    /// The presentation of nothing: no shape and no members.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            shape: Maybe::Absent(shape_parameter::Absent::Unshaped),
            sorts: Vec::new(),
            operations: Vec::new(),
            rules: Vec::new(),
        }
    }
}

/// A member's position in its list of a presentation: its sorts, operations
/// or rules.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MemberPosition(usize);

impl From<MemberPosition> for usize
{
    /// The position as an index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: MemberPosition) -> Self
    {
        position.0
    }
}

/// The inclusion of one presentation in another: where each member of the
/// included presentation stands among the including one's, each list in the
/// included presentation's order.
///
/// # Specification
/// - requires: nothing to construct this data; [`TheoryParts::include`] returns
///   one.
/// - ensures: one position per included member.
/// - executable: none — a data carrier; [`TheoryParts::restrict`] reads along
///   it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryParts::include`].
/// - witness: `theory::tests::an_extension_restricts_to_what_it_includes`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct TheoryInclusion
{
    /// Where each included sort stands.
    pub sorts: Vec<MemberPosition>,
    /// Where each included operation stands.
    pub operations: Vec<MemberPosition>,
    /// Where each included rule stands.
    pub rules: Vec<MemberPosition>,
}

/// Why one presentation does not extend another.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each variant names the first member, sorts before operations
///   before rules, that blocks the extension.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryParts::include`].
/// - witness: `theory::tests::a_member_defined_twice_blocks_the_extension_by_name`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IncludeClash
{
    /// The included presentation states a shape parameter, which is a
    /// parameter of the presentation, not a member it shares.
    Shaped,
    /// A sort of this name is present with another index telescope or
    /// representability.
    Sort(Name),
    /// An operation of this name is present with other ports.
    Operation(Name),
    /// A rule of this name is present with other sides.
    Rule(Name),
}

impl TheoryParts
{
    /// Extend these parts by `included`'s members and return the inclusion.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success each included member stands at its position in the
    ///   inclusion, a member already present under its name at that member's
    ///   position and every other one appended after these parts' members in
    ///   `included`'s order; [`Self::restrict`] along the inclusion is
    ///   `included`. On failure these parts are unchanged.
    /// - fails: a shaped `included` is [`IncludeClash::Shaped`]; a member
    ///   present under its name with another definition is the clash naming it.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first clash, sorts before operations before rules.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an extension restricts to what it includes, two
    ///   extensions of one presentation included together share its members,
    ///   and a member defined twice or a shaped presentation blocks the
    ///   extension by name, leaving the parts as they were.
    /// - witness: `theory::tests::an_extension_restricts_to_what_it_includes`
    /// - witness: `theory::tests::two_extensions_of_one_presentation_meet_along_it`
    /// - witness: `theory::tests::a_member_defined_twice_blocks_the_extension_by_name`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |inclusion| inclusion.sorts.len() == included.sorts.len() && inclusion.operations.len() == included.operations.len() && inclusion.rules.len() == included.rules.len()))]
    pub fn include(
        &mut self,
        included: &Self,
    ) -> Result<TheoryInclusion, IncludeClash>
    {
        if matches!(included.shape, Maybe::Present(_)) {
            return Err(IncludeClash::Shaped);
        }
        let (sorts, fresh_sorts) = placed(
            &self.sorts,
            &included.sorts,
            |sort| &sort.name,
            IncludeClash::Sort,
        )?;
        let (operations, fresh_operations) = placed(
            &self.operations,
            &included.operations,
            |operation| &operation.name,
            IncludeClash::Operation,
        )?;
        let (rules, fresh_rules) = placed(
            &self.rules,
            &included.rules,
            |rule| &rule.name,
            IncludeClash::Rule,
        )?;
        self.sorts.extend(fresh_sorts.into_iter().cloned());
        self.operations
            .extend(fresh_operations.into_iter().cloned());
        self.rules.extend(fresh_rules.into_iter().cloned());
        Ok(TheoryInclusion {
            sorts,
            operations,
            rules,
        })
    }

    /// The presentation these parts restrict to along `inclusion`: the
    /// members at its positions, in its order, with no shape.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each list holds the member at each of the inclusion's
    ///   positions these parts hold, in the inclusion's order; a position past
    ///   a list contributes nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::include`].
    /// - witness: `theory::tests::an_extension_restricts_to_what_it_includes`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.sorts.len() <= inclusion.sorts.len() && ret.operations.len() <= inclusion.operations.len() && ret.rules.len() <= inclusion.rules.len())]
    pub fn restrict(
        &self,
        inclusion: &TheoryInclusion,
    ) -> Self
    {
        Self {
            shape: Maybe::Absent(shape_parameter::Absent::Unshaped),
            sorts: at_positions(&self.sorts, &inclusion.sorts),
            operations: at_positions(&self.operations, &inclusion.operations),
            rules: at_positions(&self.rules, &inclusion.rules),
        }
    }
}

/// Where each of `included` stands once appended to `own`: at the position of
/// the member of its name in `own`, or after `own` in `included`'s order; and
/// the members appended.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one position per member of `included`; the appended members are
///   those of `included` whose name `own` does not hold, in order.
/// - fails: a member whose name `own` holds with another definition is `clash`
///   of its name.
/// - panics: none.
///
/// # Errors
/// Returns the first clash in `included`'s order.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryParts::include`].
/// - witness: `theory::tests::two_extensions_of_one_presentation_meet_along_it`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ref positions, ref fresh)| positions.len() == included.len() && fresh.len() <= included.len()))]
fn placed<'members, M>(
    own: &[M],
    included: &'members [M],
    name: impl Fn(&M) -> &Name,
    clash: impl Fn(Name) -> IncludeClash,
) -> Result<(Vec<MemberPosition>, Vec<&'members M>), IncludeClash>
where
    M: PartialEq,
{
    let held: BTreeMap<&Name, (usize, &M)> = own
        .iter()
        .enumerate()
        .map(|(at, mine)| (name(mine), (at, mine)))
        .collect();
    let mut positions = Vec::with_capacity(included.len());
    let mut fresh = Vec::new();
    for member in included {
        let position = match held.get(name(member)) {
            Some(&(at, mine)) if mine == member => at,
            Some(_) => return Err(clash(name(member).clone())),
            None => {
                fresh.push(member);
                own.len().saturating_add(fresh.len()).saturating_sub(1)
            },
        };
        positions.push(MemberPosition(position));
    }
    Ok((positions, fresh))
}

/// The members of `members` at `positions`, in their order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the member at each position `members` holds, in order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryParts::restrict`].
/// - witness: `theory::tests::an_extension_restricts_to_what_it_includes`
#[spec(ensures: |ret| ret.len() <= positions.len())]
fn at_positions<M>(
    members: &[M],
    positions: &[MemberPosition],
) -> Vec<M>
where
    M: Clone,
{
    positions
        .iter()
        .filter_map(|&MemberPosition(at)| members.get(at).cloned())
        .collect()
}

/// Why a value of `Theory`'s description codes no presentation.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each variant names the first place the value departs from the
///   grammar, read root first.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TheoryFault
{
    /// A constructor stands where the grammar admits another: the root is not
    /// `Presents`, a chain holds a foreign member, or a term position holds no
    /// term.
    Misplaced(ConstructorTag),
    /// A payload's shape is not its constructor's code.
    Payload,
    /// A name is not UTF-8 text.
    Text,
    /// A shape's size is not one decimal numeral, or a face's points are not
    /// decimal numerals joined by `,`, ascending and each once, each in its
    /// one spelling.
    Numeral,
}

/// A value of `Theory`: one presentation.
///
/// # Specification
/// - requires: nothing to construct this data through [`Self::encode`];
///   [`Self::from_value`] admits any value, which [`Self::decode`] judges.
/// - ensures: the value is a value of [`theory_desc`]'s description.
/// - executable: none — a data carrier; its operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Self::encode`] and [`Self::decode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryValue(DescValue);

impl TheoryValue
{
    /// The value coding `parts`.
    ///
    /// # Specification
    /// - requires: only an operation's port binds, and a binder binds nothing
    ///   of its own: the grammar has no other place for a binder.
    /// - ensures: the root is `Presents` over the sort, operation and rule
    ///   chains, each member in order, a shape as a `Shape` at the head of the
    ///   sort chain over its `Face` chain, a representable sort as
    ///   `Representable` and a port with binders as `Bound`; [`Self::decode`]
    ///   reads `parts` back.
    /// - panics: none.
    /// - intension: every chain is folded from its end and every term built
    ///   from a post-order worklist, so no step recurses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation with an indexed sort, a representable
    ///   sort, a two-output operation, an unnamed port, a port under two
    ///   binders and rules whose sides apply operations, constructors and a
    ///   results tuple round-trips exactly, a shaped presentation round-trips
    ///   with its faces, and a first-order presentation encodes to its exact
    ///   bytes; a dropped member, a swapped chain, a lost index, binder or face
    ///   or a forgotten representability changes the decoded parts or the
    ///   bytes.
    /// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
    /// - witness: `theory::tests::a_presentation_encodes_to_its_exact_identity_bytes`
    /// - witness: `theory::tests::a_second_order_presentation_encodes_its_binders`
    /// - witness: `theory::tests::a_shaped_presentation_codes_its_faces`
    #[inline]
    #[must_use]
    #[spec(
        requires: parts.sorts.iter().flat_map(|sort| sort.indices.iter()).all(|index| index.bindings.is_empty()),
        ensures: |ref value| value.0.ctor == Tag::Presents.constructor(),
    )]
    pub fn encode(parts: &TheoryParts) -> Self
    {
        let mut sorts = value(Tag::End, Vec::new());
        for sort in parts.sorts.iter().rev() {
            let indices = ports(&sort.indices);
            let tag = match sort.representability {
                Representability::Ordinary => Tag::Sort,
                Representability::Representable => Tag::Representable,
            };
            sorts = value(tag, vec![leaf(&sort.name), rec(indices), rec(sorts)]);
        }
        if let Maybe::Present(ref shape) = parts.shape {
            let mut faces = value(Tag::End, Vec::new());
            for face in shape.faces.iter().rev() {
                faces = value(Tag::Face, vec![
                    leaf(face.name()),
                    Payload::leaf(numerals(face.points()).as_bytes()),
                    rec(faces),
                ]);
            }
            sorts = value(Tag::Shape, vec![
                leaf(&shape.name),
                Payload::leaf(format!("{}", usize::from(shape.points)).as_bytes()),
                rec(faces),
                rec(sorts),
            ]);
        }
        let mut operations = value(Tag::End, Vec::new());
        for operation in parts.operations.iter().rev() {
            let inputs = ports(&operation.inputs);
            let outputs = ports(&operation.outputs);
            let tag = match operation.kind {
                OperationKind::Operation => Tag::Oper,
                OperationKind::Observation => Tag::Obs,
            };
            operations = value(tag, vec![
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

    /// A value of `Theory`'s description, whatever it codes.
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
    ///   constructor's code, a name that is not UTF-8, or a size or a face's
    ///   points not in their one numeral spelling; a `Shape` anywhere but the
    ///   head of the sort chain is misplaced, and so are a `Bound` port
    ///   anywhere but an operation's port chain, a `Bound` binder and a `Bound`
    ///   port binding nothing, so a port's value has one spelling.
    /// - panics: none.
    /// - intension: chains are walked in loops and terms rebuilt from a
    ///   post-order worklist, so no step recurses.
    ///
    /// # Errors
    /// Returns the first [`TheoryFault`] met, root first.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the round trip of a presentation exercising every
    ///   constructor, and ten malformed values — an `End` root, a rule in the
    ///   sort chain, a port where a term stands, a non-UTF-8 name, a binding
    ///   index port, a binding binder, a binderless `Bound` port, a second
    ///   `Shape`, a size of two numerals and descending face points — each
    ///   refused by its exact fault.
    /// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
    /// - witness: `theory::tests::a_second_order_presentation_encodes_its_binders`
    /// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
    /// - witness: `theory::tests::a_binder_outside_an_operation_port_is_misplaced`
    /// - witness: `theory::tests::a_shaped_presentation_codes_its_faces`
    #[inline]
    #[spec(ensures: |ref ret| ret.is_err() || self.0.ctor == Tag::Presents.constructor())]
    pub fn decode(&self) -> Result<TheoryParts, TheoryFault>
    {
        let root = Node {
            ctor: self.0.ctor,
            payload: self.0.payload.to_node(),
        };
        let [sorts, operations, rules] = expect::<3>(root, Tag::Presents)?;
        let mut parts = TheoryParts::default();
        let mut at = nested(sorts)?;
        if at.ctor == Tag::Shape.constructor() {
            let [name, size, faces, rest] = expect::<4>(at, Tag::Shape)?;
            parts.shape = Maybe::Present(read_shape(name, size, faces)?);
            at = nested(rest)?;
        }
        loop {
            let representability = if at.ctor == Tag::Representable.constructor() {
                Representability::Representable
            }
            else {
                Representability::Ordinary
            };
            let tag = match representability {
                Representability::Ordinary => Tag::Sort,
                Representability::Representable => Tag::Representable,
            };
            let next = member::<3>(at, tag)?;
            let Maybe::Present([name, indices, rest]) = next
            else {
                break;
            };
            let name = text(name)?;
            let indices = nested(indices)?;
            let indices = read_plain(indices, unbound)?;
            parts.sorts.push(TheorySort {
                name,
                indices,
                representability,
            });
            at = nested(rest)?;
        }
        let mut at = nested(operations)?;
        loop {
            let kind = if at.ctor == Tag::Obs.constructor() {
                OperationKind::Observation
            }
            else {
                OperationKind::Operation
            };
            let tag = match kind {
                OperationKind::Operation => Tag::Oper,
                OperationKind::Observation => Tag::Obs,
            };
            let next = member::<4>(at, tag)?;
            let Maybe::Present([name, inputs, outputs, rest]) = next
            else {
                break;
            };
            let name = text(name)?;
            let inputs = nested(inputs)?;
            let inputs = read_ports(inputs)?;
            let outputs = nested(outputs)?;
            let outputs = read_ports(outputs)?;
            parts.operations.push(TheoryOperation {
                name,
                kind,
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
            parts.rules.push(TheoryRule { name, left, right });
            at = nested(rest)?;
        }
        Ok(parts)
    }

    /// The value's canonical bytes: the presentation's identity.
    ///
    /// # Specification
    /// - ensures: [`serialize_value`] of the value under [`theory_desc`]'s
    ///   description; two values encode alike exactly when they are equal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation's exact bytes pin tag order, field
    ///   order and name lengths; two presentations differing in one port name
    ///   encode apart, and the same presentation read twice encodes alike.
    /// - witness: `theory::tests::a_presentation_encodes_to_its_exact_identity_bytes`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref bytes| *bytes == serialize_value(&theory_desc(()), &self.0))]
    pub fn identity(&self) -> SerializedValueBytes
    {
        serialize_value(&theory_desc(()), &self.0)
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

/// The chain coding `list`, in order: a port with binders as `Bound` over the
/// chain of its binders, every other port as `Port`.
///
/// # Specification
/// trivial.
fn ports(list: &[TheoryPort]) -> DescValue
{
    let mut chain = value(Tag::End, Vec::new());
    for port in list.iter().rev() {
        if port.bindings.is_empty() {
            chain = plain_port(&port.name, &port.sort, &port.indices, chain);
            continue;
        }
        let mut binders = value(Tag::End, Vec::new());
        for binder in port.bindings.iter().rev() {
            binders = plain_port(&binder.name, &binder.sort, &binder.indices, binders);
        }
        chain = value(Tag::Bound, vec![
            leaf(&port.name),
            leaf(&port.sort),
            rec(index_arguments(&port.indices)),
            rec(binders),
            rec(chain),
        ]);
    }
    chain
}

/// The `Port` member coding a port named `name` at `sort` over `indices`,
/// before `rest`: a port that binds nothing, or a binder.
///
/// # Specification
/// trivial.
fn plain_port(
    name: &Name,
    sort: &Name,
    indices: &[FreeTerm],
    rest: DescValue,
) -> DescValue
{
    value(Tag::Port, vec![
        leaf(name),
        leaf(sort),
        rec(index_arguments(indices)),
        rec(rest),
    ])
}

/// The argument chain over the index terms `indices`, in order.
///
/// # Specification
/// trivial.
fn index_arguments(indices: &[FreeTerm]) -> DescValue
{
    arguments(indices.iter().map(|index| term(index.to_node())).collect())
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
///   round trip of [`TheoryValue::decode`] does.
/// - intension: a post-order worklist with a stack of coded terms.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::encode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
fn term(root: TermNode<'_>) -> DescValue
{
    let mut pending = vec![Build::Visit(root)];
    let mut built: Vec<DescValue> = Vec::new();
    while let Some(step) = pending.pop() {
        match step {
            Build::Visit(node) => {
                let (tag, head, args) = match node.view() {
                    TermView::Var(name) => {
                        built.push(value(Tag::Var, vec![leaf(name)]));
                        continue;
                    },
                    TermView::Op { name, args } => (Tag::App, Maybe::Present(name), args),
                    TermView::Ctor { name, args } => (Tag::Con, Maybe::Present(name), args),
                    TermView::Results { args } => {
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
            Build::Apply(tag, head, count) => {
                let start = built.len().saturating_sub(count);
                let chain = arguments(built.split_off(start));
                built.push(match head {
                    Maybe::Present(name) => value(tag, vec![leaf(name), rec(chain)]),
                    Maybe::Absent(_) => value(tag, vec![rec(chain)]),
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
/// - fails: [`TheoryFault::Misplaced`] for another constructor;
///   [`TheoryFault::Payload`] for a payload of another shape.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| ret.is_err() || node.ctor == tag.constructor())]
fn expect<const N: usize>(
    node: Node<'_>,
    tag: Tag,
) -> Result<[PayloadNode<'_>; N], TheoryFault>
{
    if node.ctor != tag.constructor() {
        return Err(TheoryFault::Misplaced(node.ctor));
    }
    let mut fields = Vec::with_capacity(N);
    let mut rest = node.payload;
    for _ in 1 .. N {
        let PayloadView::Pair(mut halves) = rest.view()
        else {
            return Err(TheoryFault::Payload);
        };
        let (Some(left), Some(right)) = (halves.next(), halves.next())
        else {
            return Err(TheoryFault::Payload);
        };
        fields.push(left);
        rest = right;
    }
    if N > 0 {
        fields.push(rest);
    }
    <[PayloadNode<'_>; N]>::try_from(fields).map_err(|_unequal| TheoryFault::Payload)
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
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Absent(_)) => node.ctor == Tag::End.constructor(),
    | Ok(Maybe::Present(_)) => node.ctor == tag.constructor(),
    | Err(_) => true,
})]
fn member<const N: usize>(
    node: Node<'_>,
    tag: Tag,
) -> Result<Maybe<[PayloadNode<'_>; N], chained::Absent>, TheoryFault>
{
    if node.ctor == Tag::End.constructor() {
        let [] = expect::<0>(node, Tag::End)?;
        if !matches!(node.payload.view(), PayloadView::Unit) {
            return Err(TheoryFault::Payload);
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
/// - fails: [`TheoryFault::Payload`] for a field that is no recursive
///   occurrence.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| ret.is_ok() == matches!(field.view(), PayloadView::Rec { .. }))]
fn nested(field: PayloadNode<'_>) -> Result<Node<'_>, TheoryFault>
{
    let PayloadView::Rec {
        ctor,
        payload: mut inner,
    } = field.view()
    else {
        return Err(TheoryFault::Payload);
    };
    let payload = inner.next().ok_or(TheoryFault::Payload)?;
    Ok(Node { ctor, payload })
}

/// The name a `String` field holds.
///
/// # Specification
/// - ensures: the field's bytes as a name.
/// - fails: [`TheoryFault::Payload`] for a field that is no leaf;
///   [`TheoryFault::Text`] for bytes that are not UTF-8.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
#[spec(ensures: |ret| ret.is_ok() == matches!(
    field.view(),
    PayloadView::Leaf(bytes) if core::str::from_utf8(bytes.as_ref()).is_ok()
))]
fn text(field: PayloadNode<'_>) -> Result<Name, TheoryFault>
{
    let PayloadView::Leaf(bytes) = field.view()
    else {
        return Err(TheoryFault::Payload);
    };
    let spelled = core::str::from_utf8(bytes.as_ref()).map_err(|_invalid| TheoryFault::Text)?;
    Ok(Name::from(spelled))
}

/// The numerals spelling `points`, joined by `,`: a face's points field.
///
/// # Specification
/// trivial.
fn numerals(points: &[ShapePoint]) -> String
{
    let spelled: Vec<String> = points
        .iter()
        .map(|point| format!("{}", usize::from(*point)))
        .collect();
    spelled.join(",")
}

/// The points a numerals field spells.
///
/// # Specification
/// - ensures: the numbers in order when the field is decimal numerals joined by
///   `,`, strictly ascending, each in its one spelling — no sign and no leading
///   zero but `0` itself; the empty field spells none.
/// - fails: [`TheoryFault::Numeral`] for any other field, a number past the
///   machine's word among them.
/// - panics: none.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_shaped_presentation_codes_its_faces`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref points) => numerals(points) == spelled.as_ref(),
    Err(fault) => fault == TheoryFault::Numeral,
})]
fn read_numerals(spelled: &Name) -> Result<Vec<ShapePoint>, TheoryFault>
{
    let mut read: Vec<ShapePoint> = Vec::new();
    if spelled.as_ref().is_empty() {
        return Ok(read);
    }
    for numeral in spelled.as_ref().split(',') {
        let number: usize = numeral.parse().map_err(|_unread| TheoryFault::Numeral)?;
        let point = ShapePoint::from(number);
        // A parsed numeral is its one spelling unless it carries a sign or a
        // leading zero.
        let spelled_once =
            !numeral.starts_with('+') && (numeral == "0" || !numeral.starts_with('0'));
        if !spelled_once || read.last().is_some_and(|last| *last >= point) {
            return Err(TheoryFault::Numeral);
        }
        read.push(point);
    }
    Ok(read)
}

/// The shape a `Shape` member codes: its name, its size and its faces.
///
/// # Specification
/// - ensures: the shape named by `name`, of the size `size` spells, with one
///   face per `Face` member of the chain at `faces`, in order.
/// - fails: as [`text`], [`member`] and [`nested`]; [`TheoryFault::Numeral`]
///   for a size that is not one numeral or face points not in their one
///   spelling.
/// - panics: none.
/// - executable: none — a predicate would read the chain a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_shaped_presentation_codes_its_faces`
fn read_shape(
    name: PayloadNode<'_>,
    size: PayloadNode<'_>,
    faces: PayloadNode<'_>,
) -> Result<TheoryShape, TheoryFault>
{
    let name = text(name)?;
    let size = text(size)?;
    let &[points] = read_numerals(&size)?.as_slice()
    else {
        return Err(TheoryFault::Numeral);
    };
    let mut node = nested(faces)?;
    let mut read = Vec::new();
    loop {
        let next = member::<3>(node, Tag::Face)?;
        let Maybe::Present([face, members, rest]) = next
        else {
            break;
        };
        let face = text(face)?;
        let members = text(members)?;
        read.push(ShapeFace::new(face, read_numerals(&members)?));
        node = nested(rest)?;
    }
    Ok(TheoryShape::new(
        name,
        ShapeSize::from(usize::from(points)),
        read,
    ))
}

/// The ports of an operation's chain at `node`, in order, each with the
/// binders it carries.
///
/// # Specification
/// - ensures: one port per `Port` or `Bound` member, each with its index terms;
///   a `Bound` member's binders in order, a `Port` member's none.
/// - fails: as [`member`], [`text`], [`read_term`] and [`read_plain`]; a
///   `Bound` member whose binder chain is empty is misplaced at its `End`.
/// - panics: none.
/// - executable: none — a predicate would read the chain a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_second_order_presentation_encodes_its_binders`
/// - witness: `theory::tests::a_binder_outside_an_operation_port_is_misplaced`
fn read_ports(mut node: Node<'_>) -> Result<Vec<TheoryPort>, TheoryFault>
{
    let mut ports = Vec::new();
    loop {
        if node.ctor != Tag::Bound.constructor() {
            let next = member::<4>(node, Tag::Port)?;
            let Maybe::Present([name, sort, indices, rest]) = next
            else {
                break;
            };
            let port = plain_at(name, sort, indices)?;
            ports.push(unbound(port));
            node = nested(rest)?;
            continue;
        }
        let [name, sort, indices, binders, rest] = expect::<5>(node, Tag::Bound)?;
        let port = plain_at(name, sort, indices)?;
        let binders = nested(binders)?;
        if binders.ctor == Tag::End.constructor() {
            return Err(TheoryFault::Misplaced(binders.ctor));
        }
        let bindings = read_plain(binders, core::convert::identity)?;
        ports.push(TheoryPort {
            name: port.name,
            sort: port.sort,
            indices: port.indices,
            bindings,
        });
        node = nested(rest)?;
    }
    Ok(ports)
}

/// The members of a chain at `node` that bind nothing — a sort's index
/// telescope or a port's binders — in order, each read by `read`.
///
/// # Specification
/// - ensures: one member per `Port` member, each with its index terms.
/// - fails: as [`member`], [`text`] and [`read_term`]; a `Bound` member is
///   misplaced.
/// - panics: none.
/// - executable: none — a predicate would read the chain a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
/// - witness: `theory::tests::a_binder_outside_an_operation_port_is_misplaced`
fn read_plain<Read>(
    mut node: Node<'_>,
    read: fn(TheoryBinder) -> Read,
) -> Result<Vec<Read>, TheoryFault>
{
    let mut members = Vec::new();
    loop {
        let next = member::<4>(node, Tag::Port)?;
        let Maybe::Present([name, sort, indices, rest]) = next
        else {
            break;
        };
        let port = plain_at(name, sort, indices)?;
        members.push(read(port));
        node = nested(rest)?;
    }
    Ok(members)
}

/// A port that binds nothing, from the fields `plain` read.
///
/// # Specification
/// trivial.
fn unbound(plain: TheoryBinder) -> TheoryPort
{
    TheoryPort {
        name: plain.name,
        sort: plain.sort,
        indices: plain.indices,
        bindings: Vec::new(),
    }
}

/// The fields of a `Port` member: its name `name`, its sort `sort` and the
/// argument chain `indices`.
///
/// # Specification
/// - ensures: the name, the sort's name and the index terms in order.
/// - fails: as [`text`], [`nested`] and [`read_arguments`].
/// - panics: none.
/// - executable: none — a predicate would read the fields a second time.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
fn plain_at(
    name: PayloadNode<'_>,
    sort: PayloadNode<'_>,
    indices: PayloadNode<'_>,
) -> Result<TheoryBinder, TheoryFault>
{
    let name = text(name)?;
    let sort = text(sort)?;
    let indices = nested(indices)?;
    let indices = read_arguments(indices)?;
    Ok(TheoryBinder {
        name,
        sort,
        indices,
    })
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
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
fn read_arguments(node: Node<'_>) -> Result<Vec<FreeTerm>, TheoryFault>
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
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
fn argument_nodes(mut node: Node<'_>) -> Result<Vec<Node<'_>>, TheoryFault>
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
/// - fails: [`TheoryFault::Misplaced`] for any other constructor; as
///   [`expect`], [`text`] and [`argument_nodes`] beneath.
/// - panics: none.
/// - executable: none — the reading is observed by coding it again, which the
///   round trip of [`TheoryValue::decode`] does.
/// - intension: a post-order worklist with a stack of read terms.
///
/// # Errors
/// As stated.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryValue::decode`].
/// - witness: `theory::tests::a_presentation_round_trips_through_its_value`
/// - witness: `theory::tests::a_value_outside_the_grammar_is_refused_by_name`
fn read_term(root: Node<'_>) -> Result<FreeTerm, TheoryFault>
{
    let mut pending = vec![Read::Visit(root)];
    let mut read: Vec<FreeTerm> = Vec::new();
    while let Some(step) = pending.pop() {
        match step {
            Read::Visit(node) => {
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
                    return Err(TheoryFault::Misplaced(node.ctor));
                };
                let chain = nested(chain)?;
                let arguments = argument_nodes(chain)?;
                pending.push(Read::Apply(applied, arguments.len()));
                pending.extend(arguments.into_iter().rev().map(Read::Visit));
            },
            Read::Apply(applied, count) => {
                let start = read.len().saturating_sub(count);
                let arguments = read.split_off(start);
                read.push(match applied {
                    Applied::Operation(head) => FreeTerm::op(head, arguments),
                    Applied::Constructor(head) => FreeTerm::ctor(head, arguments),
                    Applied::Tuple => FreeTerm::results(arguments),
                });
            },
        }
    }
    read.pop().ok_or(TheoryFault::Payload)
}

#[cfg(test)]
mod tests;
