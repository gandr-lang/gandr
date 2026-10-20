//! The accessibility walk a data declaration passes before its fields form,
//! mirroring the kernel's.
//!
//! A declaration is admitted in a block: alone, or with the declarations a
//! mutual block admits beside it. A field may place a family of its block
//! under any placeable former — a thunk, a function's domain or codomain, a
//! returner's result, a record, product, sum, list or Σ component, a `&`
//! branch, or a strictly positive parameter of an earlier family — always at
//! the parameter variables in telescope order. A family under no function's
//! domain is strictly positive. One under a domain makes its block
//! stratified: a case puts a value's fields one stage below it, so a function
//! field takes only values below the one that holds it, and Curry's consumer,
//! which applies the field to its holder, is refused at the call as
//! `StageNotBelow`. An occurrence no stage reaches — a family at other
//! arguments, inside a term, or through a parameter its family does not hold
//! strictly positively — is refused by name. A definition of the block stands
//! for its body: a field naming one is read through it, the types the body
//! quotes at the place the definition is named and the types it only
//! annotates its terms with not at all (#602). A reference past the block's
//! last member is a reference outside the block.
//!
//! The walk returns the family's [`Accessibility`]: whether its block is
//! strictly positive or stratified, and which of its parameters it holds
//! strictly positively, so a later family may nest through them.
//!
//! A data declaration's block is what its fields reach: [`reach`] extends it
//! past every later position a member names, so a block is never declared,
//! only measured, and both checkers measure it alike.
//!
//! Both checkers run this walk before a data declaration forms and refuse by
//! the same names: `NegativeOccurrence`, `NestedOccurrence`, `IndexOccurrence`,
//! `NonUniformOccurrence` and `CrossBlockReference`, each carrying the kernel's
//! `OccurrenceSite` and each classified as malformed source. A declaration the
//! checker admits, the kernel admits on readmission; one it refuses never
//! reaches the bridge. Witness:
//! `tests::recursive_data::readmission_agrees_with_the_checker_on_every_occurrence_class`.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::ParameterPosition;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;

/// Any node of the core arena, as one ordered key.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AnyNode
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// Which side of the function arrows above it an occurrence stands on.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Polarity
{
    /// Under no function's domain: strictly positive.
    Strict,
    /// Under an even number of function domains, at least two.
    Positive,
    /// Under an odd number of function domains.
    Negative,
}

impl Polarity
{
    /// The polarity past one more function domain.
    ///
    /// # Specification
    /// trivial.
    const fn flip(self) -> Self
    {
        match self {
            Self::Strict | Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

/// Where a node stands relative to the stage the constructor rule gives a
/// field: where the stage order places an occurrence, or past its reach.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reach
{
    /// The field's own type, or a child a placeable former holds at a placed
    /// position: a uniform occurrence here stands at a stage below its
    /// constructor's.
    Placed
    {
        /// The binders crossed since the field's root.
        depth: Binders,
        /// The side of the function arrows it stands on.
        polarity: Polarity,
    },
    /// Inside a former no stage reaches through.
    Nested
    {
        /// The side of the function arrows it stands on.
        polarity: Polarity,
    },
    /// Inside a term a type reads.
    Term
    {
        /// The side of the function arrows it stands on.
        polarity: Polarity,
    },
}

impl Reach
{
    /// Where a field's own type stands.
    const FIELD: Self = Self::Placed {
        depth: Binders::NONE,
        polarity: Polarity::Strict,
    };
    /// Where a parameter's type stands: every occurrence in it is an index.
    const PARAMETER: Self = Self::Term {
        polarity: Polarity::Strict,
    };

    /// The side of the function arrows this reach stands on.
    ///
    /// # Specification
    /// trivial.
    const fn polarity(self) -> Polarity
    {
        match self {
            Self::Placed { polarity, .. } | Self::Nested { polarity } | Self::Term { polarity } => {
                polarity
            },
        }
    }

    /// The reach of a child a former no stage reaches through holds.
    ///
    /// # Specification
    /// trivial.
    const fn nest(self) -> Self
    {
        match self {
            Self::Placed { polarity, .. } | Self::Nested { polarity } => Self::Nested { polarity },
            Self::Term { polarity } => Self::Term { polarity },
        }
    }

    /// The reach of a child a type reads as a term.
    ///
    /// # Specification
    /// trivial.
    const fn term(self) -> Self
    {
        Self::Term {
            polarity: self.polarity(),
        }
    }

    /// The reach of a function's domain.
    ///
    /// # Specification
    /// trivial.
    const fn domain(self) -> Self
    {
        match self {
            Self::Placed { depth, polarity } => Self::Placed {
                depth,
                polarity: polarity.flip(),
            },
            Self::Nested { polarity } => Self::Nested {
                polarity: polarity.flip(),
            },
            Self::Term { polarity } => Self::Term {
                polarity: polarity.flip(),
            },
        }
    }

    /// The reach of a child standing under one more binder.
    ///
    /// # Specification
    /// trivial.
    fn under(self) -> Self
    {
        match self {
            Self::Placed { depth, polarity } => Self::Placed {
                depth: depth.deeper(),
                polarity,
            },
            Self::Nested { .. } | Self::Term { .. } => self,
        }
    }
}

/// What a self occurrence earns at its reach, least severe first.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Finding
{
    /// No occurrence, or only strictly positive ones the stage order places.
    Admitted,
    /// An occurrence the stage order places under a function's domain: the
    /// family is stratified.
    Stratified,
    /// An occurrence at non-parameter arguments.
    NonUniform,
    /// An occurrence nested in a former no stage reaches through.
    Nested,
    /// An occurrence inside a term a type reads.
    Index,
    /// An occurrence under a function's domain no stage reaches.
    Negative,
}

/// Whether every use of a family's parameter stands strictly positively.
///
/// A nested occurrence through a strictly positive parameter is placed: the
/// parameter stands as the decode of a field's own type or a strictly positive
/// position under it, or is handed on to a strictly positive parameter of
/// another family there.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Variance
{
    /// Every use of the parameter is strictly positive.
    StrictlyPositive,
    /// Some use is not, or the family was not walked.
    NotStrictlyPositive,
}

/// Whether a family's own occurrences all stand strictly positively.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stratification
{
    /// Every occurrence of a family of its block stands strictly positively.
    Positive,
    /// Some occurrence stands under a function's domain, at a stage below its
    /// constructor's: a case on a value at no stage reads its fields at a
    /// fresh one.
    Stratified,
}

/// What a data declaration's walk decided: how its own occurrences stand,
/// and how each of its parameters does.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `parameters` holds one variance per parameter of the walked
///   declaration.
/// - executable: none — the declaration is not held beside it.
///
/// # Adequacy
/// - hypothesis: L3 — a family with a negative field below its stage is
///   stratified, and a list's element parameter is strictly positive.
/// - witness: `tests::recursive_data::a_negative_occurrence_below_the_stage_declares`
/// - witness: `tests::recursive_data::a_nested_occurrence_through_a_strictly_positive_parameter_declares`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Accessibility
{
    /// How the family's own occurrences stand.
    stratification: Stratification,
    /// How each parameter stands, in telescope order.
    parameters: Vec<Variance>,
}

impl Accessibility
{
    /// How the family's own occurrences stand.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stratification(&self) -> Stratification
    {
        self.stratification
    }

    /// How the parameter at `parameter` stands; not strictly positive past the
    /// telescope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn variance(
        &self,
        parameter: ParameterPosition,
    ) -> Variance
    {
        self.parameters
            .get(usize::from(parameter))
            .copied()
            .unwrap_or(Variance::NotStrictlyPositive)
    }
}

/// The accessibility of the families admitted before a walk, which a nested
/// occurrence is read through.
pub trait Admitted
{
    /// How the parameter at `parameter` of the family at `family` stands; not
    /// strictly positive for a family not walked.
    ///
    /// # Specification
    /// trivial.
    fn variance(
        &self,
        family: ConstantIndex,
        parameter: ParameterPosition,
    ) -> Variance;
}

impl Admitted for alloc::collections::BTreeMap<ConstantIndex, Accessibility>
{
    /// The walked family's variance, or none.
    ///
    /// # Specification
    /// trivial.
    fn variance(
        &self,
        family: ConstantIndex,
        parameter: ParameterPosition,
    ) -> Variance
    {
        self.get(&family)
            .map_or(Variance::NotStrictlyPositive, |accessibility| {
                accessibility.variance(parameter)
            })
    }
}

/// No family walked: what a block's measure reads, which no variance moves.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unwalked;

impl Admitted for Unwalked
{
    /// Not strictly positive.
    ///
    /// # Specification
    /// trivial.
    fn variance(
        &self,
        _family: ConstantIndex,
        _parameter: ParameterPosition,
    ) -> Variance
    {
        Variance::NotStrictlyPositive
    }
}

/// Whether a self application's arguments are the parameter variables.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Uniformity
{
    /// One argument per parameter, each the parameter's variable in order.
    Uniform,
    /// Anything else.
    NonUniform,
}

/// The block a data declaration is admitted in: its families, a run of data
/// declarations from the first member, the declaration among them, then the
/// block's definitions up to the position past its last member.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a lone declaration's block holds its own family and ends one past
///   it.
/// - executable: none — the positions hold no table to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a lone family and a mutual block of a family and its
///   decoder are each walked by the block they are admitted in.
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Block
{
    /// The block's first member, its first family.
    first: ConstantIndex,
    /// The position past its last family.
    families: ConstantIndex,
    /// The position past its last member.
    end: ConstantIndex,
}

impl Block
{
    /// The block of the data declaration at `position` alone.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn lone(position: ConstantIndex) -> Self
    {
        let end = ConstantIndex::from(usize::from(position).saturating_add(1));
        Self {
            first: position,
            families: end,
            end,
        }
    }

    /// The block whose families run from `first` to before `families`, and
    /// whose definitions run from there to before `end`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn new(
        first: ConstantIndex,
        families: ConstantIndex,
        end: ConstantIndex,
    ) -> Self
    {
        Self {
            first,
            families,
            end,
        }
    }

    /// The block's first member, its first family.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn first(self) -> ConstantIndex
    {
        self.first
    }

    /// The position past the block's last family.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn families(self) -> ConstantIndex
    {
        self.families
    }

    /// Whether the block admits `position` among its families.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn family(
        self,
        position: ConstantIndex,
    ) -> Membership
    {
        if self.first <= position && position < self.families {
            Membership::Family
        }
        else {
            Membership::Other
        }
    }

    /// Whether the block holds `position` among its members.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn holds(
        self,
        position: ConstantIndex,
    ) -> Membership
    {
        if self.first <= position && position < self.end {
            Membership::Family
        }
        else {
            Membership::Other
        }
    }
}

/// Whether a position names one of a block's families, or one of its members.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Membership
{
    /// A family of the block, or a member where members are asked.
    Family,
    /// Anything else.
    Other,
}

/// The length of a declaration's parameter telescope.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Telescope(usize);

/// Where a root stands in its declaration's scope: under the parameter
/// telescope, then its constructor's `earlier` fields.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scope
{
    /// The parameter telescope.
    telescope: Telescope,
    /// The field binders between the telescope and the root.
    earlier: Binders,
}

/// Whether `arguments` begin with the parameter variables in telescope order,
/// seen from under `depth` binders past the root's scope. The arguments past
/// the telescope are an indexed family's indices, which any term may fill;
/// formation checks their number.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Uniform` exactly when there is at least one argument per
///   parameter and the `i`th, for each parameter `i`, is the intuitionistic
///   variable at distance `depth + earlier + parameters - 1 - i`, `earlier` the
///   field binders the scope holds past the telescope.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a family applied to a constant or to its parameters out
///   of order is non-uniform; `List A` applied to `A`, directly and under a
///   function field's binder, is uniform, and so is its tail past the head's
///   binder; `Vec A` applied to `A` and a length field is uniform.
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
/// - witness: `tests::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
/// - witness: `tests::native_formers::an_indexed_family_stands_at_its_indices_in_both_checkers`
#[spec(ensures: |ret| ret == Uniformity::NonUniform || arguments.len() >= scope.telescope.0)]
fn uniform(
    arena: &CoreArena,
    arguments: &[ValueId],
    depth: Binders,
    scope: Scope,
) -> Uniformity
{
    let Telescope(parameters) = scope.telescope;
    let all = arguments.len() >= parameters
        && arguments.iter().take(parameters).enumerate().all(|(position, &argument)| {
            let expected = usize::try_from(u32::from(depth))
                .ok()
                .zip(usize::try_from(u32::from(scope.earlier)).ok())
                .and_then(|(depth, earlier)| depth.checked_add(earlier))
                .and_then(|depth| depth.checked_add(parameters))
                .and_then(|scope| scope.checked_sub(position))
                .and_then(|scope| scope.checked_sub(1))
                .and_then(|distance| u32::try_from(distance).ok())
                .map(DeBruijnIndex::from);
            matches!(
                (arena.value(argument), expected),
                (Some(&Value::Variable { zone: Zone::Intuitionistic, index }), Some(wanted)) if index == wanted
            )
        });
    if all {
        Uniformity::Uniform
    }
    else {
        Uniformity::NonUniform
    }
}

/// The finding of a self occurrence at `reach`: a uniform one the stage
/// order places is admitted, and one under a function's domain stratifies
/// its family; any other is refused by its polarity, then its reach.
///
/// # Specification
/// trivial.
#[inline]
const fn found(
    reach: Reach,
    uniformity: Uniformity,
) -> Finding
{
    match (reach, uniformity) {
        (
            Reach::Placed {
                polarity: Polarity::Strict,
                ..
            },
            Uniformity::Uniform,
        ) => Finding::Admitted,
        (
            Reach::Placed {
                polarity: Polarity::Positive | Polarity::Negative,
                ..
            },
            Uniformity::Uniform,
        ) => Finding::Stratified,
        (
            Reach::Placed {
                polarity: Polarity::Negative,
                ..
            }
            | Reach::Nested {
                polarity: Polarity::Negative,
            }
            | Reach::Term {
                polarity: Polarity::Negative,
            },
            Uniformity::Uniform | Uniformity::NonUniform,
        ) => Finding::Negative,
        (
            Reach::Placed {
                polarity: Polarity::Strict | Polarity::Positive,
                ..
            },
            Uniformity::NonUniform,
        ) => Finding::NonUniform,
        (
            Reach::Nested {
                polarity: Polarity::Strict | Polarity::Positive,
            },
            Uniformity::Uniform | Uniformity::NonUniform,
        ) => Finding::Nested,
        (
            Reach::Term {
                polarity: Polarity::Strict | Polarity::Positive,
            },
            Uniformity::Uniform | Uniformity::NonUniform,
        ) => Finding::Index,
    }
}

/// Mark not strictly positive every parameter the variable at `index`, met
/// at `reach` in a root at `scope`, may name: the one it names under a placed
/// reach's known depth, and under any other every one it may name at some
/// depth.
///
/// # Specification
/// - requires: `parameters` holds the walked declaration's whole telescope.
/// - ensures: the variances of the parameters named so are not strictly
///   positive; every other is unchanged.
/// - panics: none.
/// - executable: none — the clause ranges over the mutable telescope, which a
///   predicate may not iterate; the witnesses read the variances back through
///   the families they admit and refuse.
///
/// # Adequacy
/// - hypothesis: L3 — a list's element stands only at a field's own type and
///   stays strictly positive; a parameter under a function's domain does not.
/// - witness: `tests::recursive_data::a_nested_occurrence_through_a_strictly_positive_parameter_declares`
fn mark(
    parameters: &mut [Variance],
    index: DeBruijnIndex,
    reach: Reach,
    scope: Scope,
)
{
    let Telescope(telescope) = scope.telescope;
    let Some(past) = usize::try_from(u32::from(index))
        .ok()
        .zip(usize::try_from(u32::from(scope.earlier)).ok())
        .and_then(|(index, earlier)| index.checked_sub(earlier))
    else {
        return;
    };
    let named = match reach {
        Reach::Placed { depth, .. } => usize::try_from(u32::from(depth))
            .ok()
            .and_then(|depth| past.checked_sub(depth))
            .and_then(|distance| telescope.checked_sub(distance))
            .and_then(|above| above.checked_sub(1))
            .map_or(0 .. 0, |position| position .. position.saturating_add(1)),
        Reach::Nested { .. } | Reach::Term { .. } => {
            telescope.saturating_sub(past.saturating_add(1)) .. telescope
        },
    };
    for variance in parameters.get_mut(named).into_iter().flatten() {
        *variance = Variance::NotStrictlyPositive;
    }
}

/// How the walk reads a node: as part of a field's type, or as part of the
/// body of a definition of the block the field names (#602).
///
/// A field naming a definition stands for what the definition unfolds to, so
/// the walk reads the body. A body's terms are annotated with types its uses
/// do not denote — a constructor's datatype, a case's motive — and those are
/// not read; a type the body quotes is one its use denotes, and it is read
/// as a field's type is, down to the terms inside it, which are a body's
/// terms again.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reading
{
    /// Part of a field's type: every node is read.
    Field,
    /// A term of a definition's body: its terms are read and its types are
    /// not.
    Body,
    /// A type a definition's body quotes: its types are read and its terms
    /// are a body's.
    Quoted,
}

impl Reading
{
    /// The reading of `child`, a child of a node read this way.
    ///
    /// # Specification
    /// trivial.
    const fn child(
        self,
        child: AnyNode,
    ) -> Self
    {
        match (self, child) {
            (Self::Quoted, AnyNode::Value(_) | AnyNode::Computation(_)) => Self::Body,
            (
                reading @ (Self::Field | Self::Body | Self::Quoted),
                AnyNode::Value(_)
                | AnyNode::Computation(_)
                | AnyNode::ValueType(_)
                | AnyNode::CompType(_),
            ) => reading,
        }
    }

    /// The reading of a type quoted by a term read this way.
    ///
    /// # Specification
    /// trivial.
    const fn quote(self) -> Self
    {
        match self {
            Self::Field => Self::Field,
            Self::Body | Self::Quoted => Self::Quoted,
        }
    }

    /// What `node`, read this way, is to the field: a type a body only
    /// annotates a term with is an annotation, and everything else is
    /// denoted.
    ///
    /// # Specification
    /// trivial.
    const fn denotation(
        self,
        node: AnyNode,
    ) -> Denotation
    {
        match (self, node) {
            (Self::Body, AnyNode::ValueType(_) | AnyNode::CompType(_)) => Denotation::Annotation,
            (
                Self::Field | Self::Body | Self::Quoted,
                AnyNode::Value(_)
                | AnyNode::Computation(_)
                | AnyNode::ValueType(_)
                | AnyNode::CompType(_),
            ) => Denotation::Denoted,
        }
    }
}

/// What a node the walk reaches is to the field it walks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Denotation
{
    /// Part of what the field's type denotes: read.
    Denoted,
    /// A type a definition's body annotates a term with: passed over.
    Annotation,
}

/// The walk's worklist: a node pushed is a child of the node popped last,
/// read as [`Reading::child`] says, unless pushed with a reading of its own.
struct Pending
{
    /// The nodes left, each with its reach and reading.
    items: Vec<(AnyNode, Reach, Reading)>,
    /// How the node popped last is read.
    reading: Reading,
}

impl Pending
{
    /// A worklist holding `root` alone, read as part of a field's type.
    ///
    /// # Specification
    /// trivial.
    fn new(
        root: AnyNode,
        start: Reach,
    ) -> Self
    {
        Self {
            items: Vec::from([(root, start, Reading::Field)]),
            reading: Reading::Field,
        }
    }

    /// Push `node` at `reach`, a child of the node popped last.
    ///
    /// # Specification
    /// trivial.
    fn push(
        &mut self,
        (node, reach): (AnyNode, Reach),
    )
    {
        self.items.push((node, reach, self.reading.child(node)));
    }

    /// Push `node` at `reach`, read as `reading` says.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &mut self,
        node: AnyNode,
        reach: Reach,
        reading: Reading,
    )
    {
        self.items.push((node, reach, reading));
    }

    /// The reading of the node popped last.
    ///
    /// # Specification
    /// trivial.
    const fn reading(&self) -> Reading
    {
        self.reading
    }

    /// The node pushed last; every push until the next pop is its child.
    ///
    /// # Specification
    /// trivial.
    fn pop(&mut self) -> Option<(AnyNode, Reach, Reading)>
    {
        let item = self.items.pop()?;
        self.reading = item.2;
        Some(item)
    }
}

impl Extend<(AnyNode, Reach)> for Pending
{
    /// Push every node of `iter`, each a child of the node popped last.
    ///
    /// # Specification
    /// trivial.
    fn extend<Items>(
        &mut self,
        iter: Items,
    ) where
        Items: IntoIterator<Item = (AnyNode, Reach)>,
    {
        let reading = self.reading;
        self.items.extend(
            iter.into_iter()
                .map(|(node, reach)| (node, reach, reading.child(node))),
        );
    }
}

/// The most severe occurrence of a family of `block` in one root's type, or
/// the first position past the block it names; the parameters the root uses
/// other than strictly positively marked so in `parameters`.
///
/// The stage order places an occurrence through the field's own type, a
/// thunk, a function's domain and codomain, a returner's result, the parts of
/// a product, a sum, a record, a list, a dependent pair and a lazy product,
/// and a strictly positive parameter of another family; through any other
/// former no stage reaches.
///
/// # Specification
/// - requires: `scope` is the root's scope in its declaration, `parameters`
///   holds the declaration's whole telescope, and `definitions` are the bodies
///   of the block's definitions by ascending position.
/// - ensures: `Err(index)` when the root names a position at or past the
///   block's end; otherwise the most severe finding over every occurrence of a
///   family of the block, a uniform one the stage order places finding nothing
///   when strictly positive and [`Finding::Stratified`] under a function's
///   domain, a definition of `definitions` read through its body at the reach
///   it is named at, as [`Reading`] says.
/// - provides: the declaration half of accessibility under the stage order; the
///   stage order at a consumer is the other half.
/// - fails: a position past the block, as its index.
/// - panics: none.
///
/// # Errors
/// The position past the block a reference names.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion; each node, reach and
///   reading triple is expanded once, so definitions naming each other are read
///   once each.
/// - measure: the unexpanded triples reachable from the root, finite because
///   the arena is acyclic, the definitions finite, and reaches and readings
///   finite per node.
///
/// # Adequacy
/// - hypothesis: L3 — a nested, an index and a non-uniform occurrence, a
///   negative one no stage reaches, and a reference to a later position, each
///   surface as their own finding, while the direct and function forms of
///   `Nat`, `List A` and `Tree` find nothing; a family under a function's
///   domain at a placed position stratifies, and nested under a list's strictly
///   positive element finds nothing; a decoder named in a field of its mutual
///   block finds nothing, and a family named under a domain through a
///   definition of the block is negative.
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
/// - witness: `tests::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
/// - witness: `tests::recursive_data::a_field_naming_its_own_or_a_later_position_is_refused_by_name`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
/// - witness: `tests::recursive_data::a_definition_of_the_block_is_read_through_602`
/// - witness: `tests::recursive_data::a_negative_occurrence_below_the_stage_declares`
/// - witness: `tests::recursive_data::a_nested_occurrence_through_a_strictly_positive_parameter_declares`
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|later| *later >= block.end))]
fn worst<Earlier>(
    arena: &CoreArena,
    (block, definitions, earlier): (&Block, &[(ConstantIndex, ValueId)], &Earlier),
    scope: Scope,
    (root, start): (ValueTypeId, Reach),
    parameters: &mut [Variance],
) -> Result<Finding, ConstantIndex>
where
    Earlier: Admitted + ?Sized,
{
    let mut pending = Pending::new(AnyNode::ValueType(root), start);
    let mut seen: BTreeSet<(AnyNode, Reach, Reading)> = BTreeSet::new();
    let mut worst = Finding::Admitted;
    while let Some((node, reach, reading)) = pending.pop() {
        if reading.denotation(node) == Denotation::Annotation
            || !seen.insert((node, reach, reading))
        {
            continue;
        }
        match node {
            AnyNode::ValueType(id) => match arena.value_type(id) {
                Some(&ValueType::Data {
                    declaration,
                    ref arguments,
                }) => {
                    if declaration >= block.end {
                        return Err(declaration);
                    }
                    if block.family(declaration) == Membership::Family {
                        let depth = match reach {
                            Reach::Placed { depth, .. } => depth,
                            Reach::Nested { .. } | Reach::Term { .. } => Binders::NONE,
                        };
                        let uniformity = uniform(arena, arguments, depth, scope);
                        worst = worst.max(found(reach, uniformity));
                        // A uniform application's arguments are the
                        // parameters themselves, handed on unchanged.
                        if uniformity == Uniformity::NonUniform {
                            pending.extend(
                                arguments
                                    .iter()
                                    .map(|&argument| (AnyNode::Value(argument), reach.term())),
                            );
                        }
                    }
                    else {
                        for (position, &argument) in arguments.iter().enumerate() {
                            let variance =
                                earlier.variance(declaration, ParameterPosition::from(position));
                            let placed = matches!(reach, Reach::Placed { .. })
                                && variance == Variance::StrictlyPositive;
                            match (placed, arena.value(argument), reach.polarity()) {
                                // A parameter handed on strictly positively
                                // stays strictly positive.
                                (
                                    true,
                                    Some(&Value::Variable {
                                        zone: Zone::Intuitionistic,
                                        ..
                                    }),
                                    Polarity::Strict,
                                ) => {},
                                (true, Some(&(Value::Quote(_) | Value::Variable { .. })), _) => {
                                    pending.push((AnyNode::Value(argument), reach));
                                },
                                (true | false, Some(_) | None, _) => {
                                    pending.push((AnyNode::Value(argument), reach.nest()));
                                },
                            }
                        }
                    }
                },
                Some(&ValueType::Abstract(index)) => {
                    if index >= block.end {
                        return Err(index);
                    }
                    if block.family(index) == Membership::Family {
                        worst = worst.max(found(reach.term(), Uniformity::NonUniform));
                    }
                },
                Some(&ValueType::Record(ref fields)) => {
                    pending.extend(
                        fields
                            .values()
                            .map(|&field| (AnyNode::ValueType(field), reach)),
                    );
                },
                Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                    pending.extend(parts.iter().map(|&part| (AnyNode::ValueType(part), reach)));
                },
                Some(&ValueType::Sigma { first, second }) => {
                    pending.push((AnyNode::ValueType(first), reach));
                    pending.push((AnyNode::ValueType(second), reach.under()));
                },
                Some(&ValueType::Lift { inner, .. }) => {
                    pending.push((AnyNode::ValueType(inner), reach.term()));
                },
                Some(&ValueType::StaticPi { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), reach.term()));
                    pending.push((AnyNode::ValueType(codomain), reach.term()));
                },
                Some(&ValueType::Element { code, .. }) => {
                    // A parameter decoded where the stage order places
                    // strictly positively is a strictly positive use.
                    let strict = matches!(reach, Reach::Placed {
                        polarity: Polarity::Strict,
                        ..
                    }) && matches!(
                        arena.value(code),
                        Some(&Value::Variable {
                            zone: Zone::Intuitionistic,
                            ..
                        })
                    );
                    if !strict {
                        pending.push((AnyNode::Value(code), reach.term()));
                    }
                },
                Some(&ValueType::PathUniverse(source, target)) => {
                    pending.push((AnyNode::Value(source), reach.term()));
                    pending.push((AnyNode::Value(target), reach.term()));
                },
                Some(&ValueType::Path {
                    carrier,
                    left,
                    right,
                }) => {
                    pending.push((AnyNode::ValueType(carrier), reach.nest()));
                    pending.push((AnyNode::Value(left), reach.term()));
                    pending.push((AnyNode::Value(right), reach.term()));
                },
                Some(&ValueType::Flow {
                    carrier,
                    source,
                    target,
                }) => {
                    pending.push((AnyNode::ValueType(carrier), reach.nest()));
                    pending.push((AnyNode::Value(source), reach.term()));
                    pending.push((AnyNode::Value(target), reach.term()));
                },
                Some(&ValueType::Run(session)) => {
                    pending.push((AnyNode::Value(session), reach.term()));
                },
                Some(&ValueType::Thunk(body)) => {
                    pending.push((AnyNode::CompType(body), reach));
                },
                Some(&ValueType::List(element)) => {
                    pending.push((AnyNode::ValueType(element), reach));
                },
                // A stage refines its base without moving it.
                Some(&ValueType::Staged { base, .. }) => {
                    pending.push((AnyNode::ValueType(base), reach));
                },
                Some(&ValueType::Stack { input, output }) => {
                    pending.push((AnyNode::CompType(input), Reach::Nested {
                        polarity: Polarity::Negative,
                    }));
                    pending.push((AnyNode::CompType(output), reach.nest()));
                },
                // A payload is sent as well as received: read it at a domain
                // no stage reaches, the conservative polarity.
                Some(&ValueType::Session(ref session)) => {
                    pending.extend(session.payloads().iter().map(|&payload| {
                        (AnyNode::ValueType(payload), Reach::Nested {
                            polarity: Polarity::Negative,
                        })
                    }));
                },
                Some(&ValueType::Capability { ref authority, .. }) => {
                    pending.extend(
                        authority
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), reach.nest())),
                    );
                },
                // A handle is a former no stage reaches through: what it
                // holds stands nested.
                Some(&ValueType::World(ref world)) => {
                    pending.extend(
                        world
                            .types()
                            .map(|inner| (AnyNode::ValueType(inner), reach.nest())),
                    );
                },
                Some(&(ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Unknown))
                | None => {},
            },
            AnyNode::CompType(id) => match arena.comp_type(id) {
                Some(&CompType::Arrow { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), reach.domain()));
                    pending.push((AnyNode::CompType(codomain), reach));
                },
                Some(&CompType::Pi { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), reach.domain()));
                    pending.push((AnyNode::CompType(codomain), reach.under()));
                },
                Some(&CompType::Returner {
                    result,
                    ref effects,
                }) => {
                    pending.push((AnyNode::ValueType(result), reach));
                    pending.extend(
                        effects
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), reach.nest())),
                    );
                },
                Some(&CompType::With(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| (AnyNode::CompType(component), reach)),
                    );
                },
                Some(&CompType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), reach.term()));
                },
                // A codata declaration's parameters have no variance its
                // admission decides: what its arguments name stands nested.
                Some(&CompType::Codata {
                    declaration,
                    ref arguments,
                }) => {
                    if declaration >= block.end {
                        return Err(declaration);
                    }
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), reach.nest())),
                    );
                },
                Some(&CompType::Unknown) | None => {},
            },
            AnyNode::Value(id) => match arena.value(id) {
                Some(&Value::Constant(index)) => {
                    if index >= block.end {
                        return Err(index);
                    }
                    if block.family(index) == Membership::Family {
                        worst = worst.max(found(reach.term(), Uniformity::NonUniform));
                    }
                    // A definition of the block is read through: what its
                    // body names, the field names where it names the
                    // definition (#602).
                    else if let Ok(position) =
                        definitions.binary_search_by_key(&index, |&(defined, _)| defined)
                        && let Some(&(_, body)) = definitions.get(position)
                    {
                        pending.read(AnyNode::Value(body), reach, Reading::Body);
                    }
                },
                Some(&Value::Constructor {
                    datatype,
                    ref fields,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(datatype), reach));
                    pending.extend(fields.iter().map(|&field| (AnyNode::Value(field), reach)));
                },
                Some(&Value::Record(ref fields)) => {
                    pending.extend(fields.values().map(|&field| (AnyNode::Value(field), reach)));
                },
                Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(path_type), reach));
                    pending.push((AnyNode::Value(forward), reach));
                    pending.push((AnyNode::Value(backward), reach));
                },
                Some(&Value::Tuple(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| (AnyNode::Value(component), reach)),
                    );
                },
                Some(&Value::Recorded(ref moves)) => {
                    pending.extend(
                        moves
                            .iter()
                            .filter_map(|movement| match movement.payload() {
                                Maybe::Present(payload) => Some((AnyNode::Value(payload), reach)),
                                Maybe::Absent(_) => None,
                            }),
                    );
                },
                Some(
                    &(Value::PathProduct(first, second)
                    | Value::Funext(first, second)
                    | Value::Equiv(first, second)
                    | Value::Univalence(first, second)
                    | Value::Then(first, second)
                    | Value::FlowProduct(first, second)
                    | Value::FunctionFlow(first, second)
                    | Value::SessionRelated {
                        source: first,
                        target: second,
                        ..
                    }
                    | Value::Ua {
                        forward: first,
                        backward: second,
                        ..
                    }
                    | Value::ListCons(first, second)
                    | Value::StaticApplication(first, second)),
                ) => {
                    pending.push((AnyNode::Value(first), reach));
                    pending.push((AnyNode::Value(second), reach));
                },
                Some(&Value::Reify(ref frames)) => {
                    for frame in frames.iter() {
                        match *frame {
                            StackFrame::Apply(value) => {
                                pending.push((AnyNode::Value(value), reach));
                            },
                            StackFrame::Bind(body) => {
                                pending.push((AnyNode::Computation(body), reach));
                            },
                            StackFrame::Project(_) => {},
                        }
                    }
                },
                Some(
                    &(Value::PathRefl(body)
                    | Value::Here(body)
                    | Value::Stay(body)
                    | Value::Forward(body)
                    | Value::Injection(_, body)
                    | Value::Lift { body, .. }
                    | Value::StaticLambda(body)
                    | Value::Mark { body, .. }),
                ) => {
                    pending.push((AnyNode::Value(body), reach));
                },
                Some(
                    &(Value::Thunk(body)
                    | Value::Returned(body)
                    | Value::Nested(body)
                    | Value::Run(body)),
                ) => {
                    pending.push((AnyNode::Computation(body), reach));
                },
                // A quoted type is a type its term denotes: in a definition's
                // body, it is read as a field's type is.
                Some(&Value::Quote(quoted)) => {
                    let reading = pending.reading().quote();
                    pending.read(AnyNode::ValueType(quoted), reach, reading);
                },
                Some(&Value::QuoteComputation(quoted)) => {
                    let reading = pending.reading().quote();
                    pending.read(AnyNode::CompType(quoted), reach, reading);
                },
                // A parameter of the walked declaration used anywhere a
                // strictly positive use was not read is not strictly
                // positive; a definition's body names none.
                Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index,
                }) => {
                    if reading == Reading::Field {
                        mark(parameters, index, reach, scope);
                    }
                },
                Some(
                    &(Value::Primitive { .. }
                    | Value::Variable { .. }
                    | Value::ListNil
                    | Value::Literal(_)
                    | Value::Hole(_)),
                )
                | None => {},
            },
            AnyNode::Computation(id) => match arena.computation(id) {
                Some(&Computation::DataCase {
                    scrutinee,
                    motive,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), reach));
                    pending.push((AnyNode::CompType(motive), reach));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&branch| (AnyNode::Computation(branch), reach)),
                    );
                },
                Some(&Computation::Primitive { ref arguments, .. }) => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), reach)),
                    );
                },
                Some(
                    &(Computation::RecordProjection(value, _)
                    | Computation::TupleProjection(value, _)
                    | Computation::Return(value)
                    | Computation::Force(value)),
                ) => {
                    pending.push((AnyNode::Value(value), reach));
                },
                Some(
                    &(Computation::Lambda(body)
                    | Computation::Fixpoint { body, .. }
                    | Computation::Mark { body, .. }
                    | Computation::Reset(body)
                    | Computation::Shift(body)
                    | Computation::Project(_, body)),
                ) => {
                    pending.push((AnyNode::Computation(body), reach));
                },
                Some(&Computation::With(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| (AnyNode::Computation(component), reach)),
                    );
                },
                Some(&Computation::Ascribe { body, ty }) => {
                    pending.push((AnyNode::Computation(body), reach));
                    pending.push((AnyNode::CompType(ty), reach));
                },
                Some(
                    &(Computation::Resume(stack, body)
                    | Computation::Split {
                        scrutinee: stack,
                        body,
                        ..
                    }),
                ) => {
                    pending.push((AnyNode::Value(stack), reach));
                    pending.push((AnyNode::Computation(body), reach));
                },
                Some(&Computation::Perform {
                    ref signature,
                    payload,
                    ..
                }) => {
                    pending.push((AnyNode::Value(payload), reach));
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), reach)),
                    );
                },
                Some(&Computation::Exercise {
                    capability,
                    ref signature,
                    payload,
                    ..
                }) => {
                    pending.push((AnyNode::Value(capability), reach));
                    pending.push((AnyNode::Value(payload), reach));
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), reach)),
                    );
                },
                Some(
                    &(Computation::Handle {
                        ref signature,
                        subject,
                        on_return,
                        ref clauses,
                    }
                    | Computation::Scope {
                        ref signature,
                        subject,
                        on_return,
                        ref clauses,
                    }),
                ) => {
                    pending.push((AnyNode::Computation(subject), reach));
                    pending.push((AnyNode::Computation(on_return), reach));
                    pending.extend(
                        clauses
                            .iter()
                            .map(|clause| (AnyNode::Computation(clause.body), reach)),
                    );
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), reach)),
                    );
                },
                Some(&Computation::ListFold {
                    element,
                    result,
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    pending.push((AnyNode::ValueType(element), reach));
                    pending.push((AnyNode::ValueType(result), reach));
                    pending.push((AnyNode::Value(list), reach));
                    pending.push((AnyNode::Computation(on_nil), reach));
                    pending.push((AnyNode::Computation(on_cons), reach));
                },
                Some(&Computation::ListCase {
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    pending.push((AnyNode::Value(list), reach));
                    pending.push((AnyNode::Computation(on_nil), reach));
                    pending.push((AnyNode::Computation(on_cons), reach));
                },
                Some(&Computation::Application(head, argument)) => {
                    pending.push((AnyNode::Computation(head), reach));
                    pending.push((AnyNode::Value(argument), reach));
                },
                Some(&Computation::Bind(bound, body)) => {
                    pending.push((AnyNode::Computation(bound), reach));
                    pending.push((AnyNode::Computation(body), reach));
                },
                Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), reach));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&branch| (AnyNode::Computation(branch), reach)),
                    );
                },
                Some(&Computation::Transport(path, value)) => {
                    pending.push((AnyNode::Value(path), reach));
                    pending.push((AnyNode::Value(value), reach));
                },
                Some(
                    &(Computation::PathTransport {
                        motive,
                        path,
                        value,
                    }
                    | Computation::Ride {
                        motive,
                        flow: path,
                        value,
                    }),
                ) => {
                    pending.push((AnyNode::ValueType(motive), reach.term()));
                    pending.push((AnyNode::Value(path), reach));
                    pending.push((AnyNode::Value(value), reach));
                },
                Some(&Computation::TelescopeTransport {
                    motive,
                    path,
                    start,
                    over,
                    value,
                }) => {
                    pending.push((AnyNode::CompType(motive), reach.term()));
                    pending.extend(
                        [path, start, over, value].map(|child| (AnyNode::Value(child), reach)),
                    );
                },
                Some(&Computation::Session(ref action)) => {
                    pending.extend(action.values().map(|value| (AnyNode::Value(value), reach)));
                    pending.extend(
                        action
                            .value_types()
                            .map(|ty| (AnyNode::ValueType(ty), reach.term())),
                    );
                    pending.extend(
                        action
                            .computations()
                            .map(|child| (AnyNode::Computation(child), reach)),
                    );
                },
                Some(&Computation::Memory(ref form)) => {
                    pending.extend(form.values().map(|value| (AnyNode::Value(value), reach)));
                    pending.extend(
                        form.computations()
                            .map(|child| (AnyNode::Computation(child), reach)),
                    );
                },
                Some(&Computation::World(ref form)) => {
                    pending.extend(form.values().map(|value| (AnyNode::Value(value), reach)));
                    pending.extend(
                        form.computations()
                            .map(|child| (AnyNode::Computation(child), reach)),
                    );
                },
                Some(&Computation::Hole(_)) | None => {},
            },
        }
    }
    Ok(worst)
}

/// The refusal a finding earns at one site.
///
/// # Specification
/// trivial.
#[inline]
const fn refusal(
    finding: Finding,
    site: OccurrenceSite,
) -> Result<(), CheckRefusal>
{
    match finding {
        Finding::Admitted | Finding::Stratified => Ok(()),
        Finding::NonUniform => Err(CheckRefusal::NonUniformOccurrence(site)),
        Finding::Nested => Err(CheckRefusal::NestedOccurrence(site)),
        Finding::Index => Err(CheckRefusal::IndexOccurrence(site)),
        Finding::Negative => Err(CheckRefusal::NegativeOccurrence(site)),
    }
}

/// Decide a data declaration's accessibility under the stage order: refuse
/// every occurrence of a family of `block` the stage order cannot place
/// below the constructor, and every reference past the block.
///
/// # Specification
/// - requires: `block` holds the admission position the declaration takes among
///   its families, `definitions` the bodies of its definitions by ascending
///   position, `earlier` the accessibility of the families admitted before it,
///   and `signature`'s parameters and fields are scoped as the signature
///   states.
/// - ensures: success exactly when no parameter names a family of the block,
///   every field names one only where the stage order places it — under the
///   placeable formers [`worst`] names, through a strictly positive parameter
///   of a family admitted before — always at the parameter variables in order,
///   a definition of the block counting as the types its body quotes, and
///   nothing names a position past the block; then the accessibility found:
///   [`Stratification::Stratified`] exactly when some occurrence stands under a
///   function's domain, and each parameter strictly positive exactly when every
///   use of it is.
/// - provides: the declaration half of accessibility under the stage order: a
///   positive occurrence stands at `≤` the constructor's stage and a negative
///   one strictly below it, and the stage order refuses at a consumer what no
///   declaration refuses; it runs before any field forms, as the kernel's does,
///   so both checkers refuse the same site by the same name.
/// - fails: the first site in parameter-then-field order that refuses.
/// - panics: none.
///
/// # Errors
/// `CrossBlockReference`, `NegativeOccurrence`, `IndexOccurrence`,
/// `NestedOccurrence` or `NonUniformOccurrence` at the refused site; a
/// parameter naming a family is always an index occurrence.
///
/// # Adequacy
/// - hypothesis: L3 — `Nat`, `List A` and `Tree` with a function field are
///   admitted positive; a `T → A` field domain is admitted stratified; a node
///   over a list of nodes is admitted positive; a non-uniform head, a later
///   reference, a nested, an index and a negative occurrence no stage reaches
///   are each refused by name at their site, by this checker and by the kernel;
///   a universe naming its decoder in a field is admitted with the decoder in
///   its block; a family named under a domain through a definition of its block
///   is refused.
/// - witness: `tests::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
/// - witness: `tests::recursive_data::a_definition_of_the_block_is_read_through_602`
/// - witness: `tests::recursive_data::a_negative_occurrence_below_the_stage_declares`
/// - witness: `tests::recursive_data::a_nested_occurrence_through_a_strictly_positive_parameter_declares`
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|refusal| matches!(refusal,
    CheckRefusal::CrossBlockReference { .. }
    | CheckRefusal::NegativeOccurrence(_)
    | CheckRefusal::IndexOccurrence(_)
    | CheckRefusal::NestedOccurrence(_)
    | CheckRefusal::NonUniformOccurrence(_)),
    |accessibility| accessibility.parameters.len() == signature.parameters().len()))]
pub fn occurrences<Earlier>(
    arena: &CoreArena,
    (block, definitions, earlier): (&Block, &[(ConstantIndex, ValueId)], &Earlier),
    signature: &DataSignature,
) -> Result<Accessibility, CheckRefusal>
where
    Earlier: Admitted + ?Sized,
{
    let mut parameters = alloc::vec![Variance::StrictlyPositive; signature.parameters().len()];
    let mut stratification = Stratification::Positive;
    for (index, &parameter) in signature.parameters().iter().enumerate() {
        let site = OccurrenceSite::Parameter(ParameterPosition::from(index));
        let scope = Scope {
            telescope: Telescope(index),
            earlier: Binders::NONE,
        };
        let finding = worst(
            arena,
            (block, definitions, earlier),
            scope,
            (parameter, Reach::PARAMETER),
            &mut parameters,
        )
        .map_err(|later| CheckRefusal::CrossBlockReference { site, index: later })?;
        if finding != Finding::Admitted {
            return Err(CheckRefusal::IndexOccurrence(site));
        }
    }
    let telescope = Telescope(signature.parameters().len());
    for (tag, fields) in signature.constructors().iter().enumerate() {
        let mut prior = Binders::NONE;
        for (field, &root) in fields.iter().enumerate() {
            let site = OccurrenceSite::Field {
                tag: ConstructorTag::from(tag),
                field: FieldPosition::from(field),
            };
            let scope = Scope {
                telescope,
                earlier: prior,
            };
            let finding = worst(
                arena,
                (block, definitions, earlier),
                scope,
                (root, Reach::FIELD),
                &mut parameters,
            )
            .map_err(|later| CheckRefusal::CrossBlockReference { site, index: later })?;
            refusal(finding, site)?;
            if finding == Finding::Stratified {
                stratification = Stratification::Stratified;
            }
            prior = prior.deeper();
        }
    }
    Ok(Accessibility {
        stratification,
        parameters,
    })
}

/// The position past the furthest one the data declaration at `position`
/// names: the end of the block its fields reach.
///
/// # Specification
/// - requires: `position` is the admission position the declaration takes.
/// - ensures: one past `position` when nothing in `signature` names a later
///   position; otherwise one past the furthest later position a parameter or a
///   field names.
/// - provides: how a block is measured rather than declared: a data declaration
///   naming a later declaration is admitted with it, and the kernel measures
///   the same block by the same walk.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: each root's walk restarts only past a later position it found, and
///   the block's end rises strictly each time.
/// - measure: the later positions the root names, finite.
///
/// # Adequacy
/// - hypothesis: L3 — a lone family reaches one past itself, and a universe
///   naming its decoder reaches one past the decoder.
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
#[spec(ensures: |ret| ret > position)]
pub fn reach(
    arena: &CoreArena,
    position: ConstantIndex,
    signature: &DataSignature,
) -> ConstantIndex
{
    let mut block = Block::lone(position);
    let mut unread = alloc::vec![Variance::StrictlyPositive; signature.parameters().len()];
    let telescope = Telescope(signature.parameters().len());
    let parameters = signature
        .parameters()
        .iter()
        .enumerate()
        .map(|(index, &root)| (root, Telescope(index), Binders::NONE, Reach::PARAMETER));
    let fields = signature.constructors().iter().flat_map(|fields| {
        fields.iter().enumerate().map(move |(field, &root)| {
            let earlier = (0 .. field).fold(Binders::NONE, |earlier, _| earlier.deeper());
            (root, telescope, earlier, Reach::FIELD)
        })
    });
    for (root, telescope, earlier, start) in parameters.chain(fields) {
        let scope = Scope { telescope, earlier };
        while let Err(later) = worst(
            arena,
            (&block, &[], &Unwalked),
            scope,
            (root, start),
            &mut unread,
        ) {
            block.end = ConstantIndex::from(usize::from(later).saturating_add(1));
        }
    }
    block.end
}
