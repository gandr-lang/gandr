//! The strict-positivity walk a data declaration passes before its fields form.
//!
//! A declaration is admitted in a block: alone, or with the declarations a
//! mutual block admits beside it, its families a run of data declarations at
//! the block's head and its definitions after them. A field may name a family
//! of its block in exactly two forms — directly, `T ps`, or as the codomain of
//! a thunked function whose domains do not name it, `U (Π ȳ. F (T ps))` — and
//! always at the parameter variables in telescope order. Every other
//! occurrence of a family is refused by name. A definition of the block stands
//! for its body: a field naming one is read through it, the types the body
//! quotes at the place the definition is named and the types it only
//! annotates its terms with not at all (#602). A reference past the block's
//! last member is a reference outside the block. The block is what its
//! families' fields reach — [`reach`] measures it, the same walk the checker
//! measures it by — so it is never declared, only measured.
//!
//! The walk reads every parameter and field before formation and refuses, at
//! the parameter or field site:
//!
//! - an occurrence under a function's domain, `NegativeOccurrence`;
//! - one inside another family's arguments or a field-local positive former,
//!   `NestedOccurrence`;
//! - one inside a term a type reads, or in the parameter telescope,
//!   `IndexOccurrence`;
//! - the family applied to any other arguments, `NonUniformOccurrence`;
//! - a field naming a position after its own block, `CrossBlockReference`.
//!
//! Formation then reads the self occurrence through the block's own
//! signature. Every other reference still sees only the admitted prefix. The
//! criteria are strict positivity with uniform parameters (Thierry Coquand and
//! Christine Paulin, "Inductively defined types", COLOG-88, LNCS 417, 1990,
//! `doi:10.1007/3-540-52335-9_47`), within the formation criteria of
//! inductive families (Peter Dybjer, "Inductive families", Formal Aspects of
//! Computing 6, 1994, `doi:10.1007/BF01211308`). The fixpoint the admitted
//! family recurses through is in the sibling `descent` module.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::ParameterPosition;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::error::KernelError;
use crate::rewrite::BinderDepth;

/// Which head a [`Reach::Head`] stands at.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum HeadSite
{
    /// The field's own type, the one place a thunk opens a function.
    Field,
    /// The type a function codomain returns.
    Codomain,
}

/// Where a node stands relative to the two admitted recursive field forms.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reach
{
    /// A field's own type, or the type a function codomain returns, under
    /// `depth` binders: a uniform self application is admitted here.
    Head
    {
        /// The binders crossed since the field's root.
        depth: BinderDepth,
        /// Which head this is.
        site: HeadSite,
    },
    /// The computation type under the field's thunk, before any domain.
    Thunk,
    /// The computation type past at least one function domain, under `depth`
    /// binders.
    Chain
    {
        /// The binders crossed since the field's root.
        depth: BinderDepth,
    },
    /// Under a function's domain, at any depth.
    Domain,
    /// Inside another family's arguments or under a field-local former.
    Nested,
    /// Inside a term a type reads.
    Term,
}

/// What a self occurrence earns at its reach, least severe first.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Finding
{
    /// No refused occurrence.
    Admitted,
    /// A head occurrence at non-parameter arguments.
    NonUniform,
    /// An occurrence nested in another former.
    Nested,
    /// An occurrence inside a term a type reads.
    Index,
    /// An occurrence under a function's domain.
    Negative,
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
    earlier: BinderDepth,
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
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name`
/// - witness: `recursive_data::recursive_data::a_mutual_block_is_admitted`
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
    pub(crate) fn lone(position: ConstantIndex) -> Self
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
    pub(crate) const fn new(
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

    /// The block's first member.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn first(self) -> ConstantIndex
    {
        self.first
    }

    /// The position past the block's last family.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn families(self) -> ConstantIndex
    {
        self.families
    }

    /// What `position` is in the block: one of its families, one of its
    /// definitions, or outside it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn membership(
        self,
        position: ConstantIndex,
    ) -> Membership
    {
        if position < self.first || position >= self.end {
            Membership::Other
        }
        else if position < self.families {
            Membership::Family
        }
        else {
            Membership::Definition
        }
    }
}

/// What a position is in a block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Membership
{
    /// A family of the block, in scope while the block's families form.
    Family,
    /// A definition of the block, foreseen at its declared type while the
    /// block's families form.
    Definition,
    /// Outside the block.
    Other,
}

impl From<Telescope> for Scope
{
    /// A root standing directly under the telescope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(telescope: Telescope) -> Self
    {
        Self {
            telescope,
            earlier: BinderDepth::NONE,
        }
    }
}

/// The reach of a child that nests inside a former at `reach`.
///
/// # Specification
/// trivial.
#[inline]
const fn nest(reach: Reach) -> Reach
{
    match reach {
        Reach::Domain => Reach::Domain,
        Reach::Term => Reach::Term,
        Reach::Head { .. } | Reach::Thunk | Reach::Chain { .. } | Reach::Nested => Reach::Nested,
    }
}

/// The reach of a child a type reads as a term, from a former at `reach`.
///
/// # Specification
/// trivial.
#[inline]
const fn term(reach: Reach) -> Reach
{
    match reach {
        Reach::Domain => Reach::Domain,
        Reach::Head { .. } | Reach::Thunk | Reach::Chain { .. } | Reach::Nested | Reach::Term => {
            Reach::Term
        },
    }
}

/// Whether `arguments` are the parameter variables in telescope order, seen
/// from under `depth` binders past the root's scope.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Uniform` exactly when there is one argument per parameter and
///   the `i`th is the variable at distance `depth + earlier + parameters - 1 -
///   i`, `earlier` the field binders the scope holds past the telescope.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a family applied to a constant or to the parameters out
///   of order is non-uniform; `List A` applied to `A`, directly and under a
///   function field's binder, is uniform, and so is its tail past the head's
///   binder.
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name`
/// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted`
#[spec(ensures: |ret| ret == Uniformity::NonUniform || arguments.len() == scope.telescope.0)]
fn uniform(
    arena: &TermArena,
    arguments: &[ValueId],
    depth: BinderDepth,
    scope: Scope,
) -> Uniformity
{
    let Telescope(parameters) = scope.telescope;
    let all = arguments.len() == parameters
        && arguments.iter().enumerate().all(|(position, &argument)| {
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
                (Some(&Value::Variable(found)), Some(wanted)) if found == wanted
            )
        });
    if all {
        Uniformity::Uniform
    }
    else {
        Uniformity::NonUniform
    }
}

/// The finding of a self occurrence at `reach`.
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
        (Reach::Domain, _) => Finding::Negative,
        (Reach::Term, _) => Finding::Index,
        (Reach::Nested | Reach::Thunk | Reach::Chain { .. }, _) => Finding::Nested,
        (Reach::Head { .. }, Uniformity::Uniform) => Finding::Admitted,
        (Reach::Head { .. }, Uniformity::NonUniform) => Finding::NonUniform,
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
/// the first position past the block it names.
///
/// # Specification
/// - requires: `telescope` is the declaration's telescope length and `root` is
///   scoped under it; `definitions` are the bodies of the block's definitions
///   by position.
/// - ensures: `Err(index)` when the root names a position at or past the
///   block's end; otherwise the most severe finding over every occurrence of a
///   family of the block, with the two admitted forms finding nothing, a
///   definition of `definitions` read through its body at the reach it is named
///   at, as [`Reading`] says.
/// - provides: the syntactic half of strict positivity; formation is the other
///   half.
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
/// - hypothesis: L3 — a negative, a nested, an index and a non-uniform
///   occurrence, and a reference to a later position, each surface as their own
///   finding, while the direct and function forms of `Nat`, `List A` and `Tree`
///   find nothing; a decoder named in a field of its mutual block finds
///   nothing, and a family named under a domain through a definition of the
///   block is negative.
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name`
/// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted`
/// - witness: `recursive_data::recursive_data::a_mutual_block_is_admitted`
/// - witness: `recursive_data::recursive_data::a_definition_of_the_block_is_read_through_602`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|later| *later >= block.end))]
fn worst(
    arena: &TermArena,
    block: Block,
    definitions: &[(ConstantIndex, ValueId)],
    scope: Scope,
    root: ValueTypeId,
    start: Reach,
) -> Result<Finding, ConstantIndex>
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
                    let inner = if block.membership(declaration) == Membership::Family {
                        let depth = match reach {
                            Reach::Head { depth, .. } => depth,
                            Reach::Thunk
                            | Reach::Chain { .. }
                            | Reach::Domain
                            | Reach::Nested
                            | Reach::Term => BinderDepth::NONE,
                        };
                        let admitted = uniform(arena, arguments, depth, scope);
                        worst = worst.max(found(reach, admitted));
                        term(reach)
                    }
                    else {
                        nest(reach)
                    };
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), inner)),
                    );
                },
                Some(&ValueType::Abstract(index)) => {
                    if index >= block.end {
                        return Err(index);
                    }
                    if block.membership(index) == Membership::Family {
                        worst = worst.max(found(term(reach), Uniformity::NonUniform));
                    }
                },
                Some(&ValueType::Record(ref fields)) => {
                    pending.extend(
                        fields
                            .values()
                            .map(|&field| (AnyNode::ValueType(field), nest(reach))),
                    );
                },
                Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                    pending.extend(
                        parts
                            .iter()
                            .map(|&part| (AnyNode::ValueType(part), nest(reach))),
                    );
                },
                // A dependent pair's factors are nested positions, as a
                // product's parts are.
                Some(&ValueType::Sigma { first, second }) => {
                    pending.push((AnyNode::ValueType(first), nest(reach)));
                    pending.push((AnyNode::ValueType(second), nest(reach)));
                },
                Some(
                    &(ValueType::List(inner)
                    | ValueType::Session {
                        payloads: inner, ..
                    }),
                ) => {
                    pending.push((AnyNode::ValueType(inner), nest(reach)));
                },
                Some(&ValueType::Lift { inner, .. }) => {
                    pending.push((AnyNode::ValueType(inner), term(reach)));
                },
                Some(&ValueType::StaticPi { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), term(reach)));
                    pending.push((AnyNode::ValueType(codomain), term(reach)));
                },
                Some(&ValueType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), term(reach)));
                },
                Some(
                    &ValueType::PathUniverse(source, target)
                    | &ValueType::FlowUniverse(source, target),
                ) => {
                    pending.push((AnyNode::Value(source), term(reach)));
                    pending.push((AnyNode::Value(target), term(reach)));
                },
                // An identity over the declaration being formed is no strictly
                // positive field: every part of a path or flow type is a term
                // position.
                Some(
                    &(ValueType::Path {
                        domain,
                        left,
                        right,
                    }
                    | ValueType::Flow {
                        domain,
                        source: left,
                        target: right,
                    }),
                ) => {
                    pending.push((AnyNode::ValueType(domain), term(reach)));
                    pending.push((AnyNode::Value(left), term(reach)));
                    pending.push((AnyNode::Value(right), term(reach)));
                },
                Some(&ValueType::Thunk(body)) => {
                    let inner = match reach {
                        Reach::Head {
                            site: HeadSite::Field,
                            ..
                        } => Reach::Thunk,
                        Reach::Head {
                            site: HeadSite::Codomain,
                            ..
                        }
                        | Reach::Thunk
                        | Reach::Chain { .. }
                        | Reach::Domain
                        | Reach::Nested
                        | Reach::Term => nest(reach),
                    };
                    pending.push((AnyNode::CompType(body), inner));
                },
                // A stage refines its base's values and never its shape: the
                // base stands where the staged type does.
                Some(&ValueType::Staged { base, .. }) => {
                    pending.push((AnyNode::ValueType(base), reach));
                },
                Some(&(ValueType::Base(_) | ValueType::Universe { .. })) | None => {},
            },
            AnyNode::CompType(id) => match arena.comp_type(id) {
                Some(&CompType::Arrow { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), Reach::Domain));
                    let inner = match reach {
                        Reach::Thunk => Reach::Chain {
                            depth: BinderDepth::NONE,
                        },
                        Reach::Chain { depth } => Reach::Chain { depth },
                        Reach::Head { .. } | Reach::Domain | Reach::Nested | Reach::Term => reach,
                    };
                    pending.push((AnyNode::CompType(codomain), inner));
                },
                Some(&CompType::Pi { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), Reach::Domain));
                    let inner = match reach {
                        Reach::Thunk => Reach::Chain {
                            depth: BinderDepth::NONE.deeper(),
                        },
                        Reach::Chain { depth } => Reach::Chain {
                            depth: depth.deeper(),
                        },
                        Reach::Head { .. } | Reach::Domain | Reach::Nested | Reach::Term => reach,
                    };
                    pending.push((AnyNode::CompType(codomain), inner));
                },
                Some(&CompType::Returner(result)) => {
                    let inner = match reach {
                        Reach::Chain { depth } => Reach::Head {
                            depth,
                            site: HeadSite::Codomain,
                        },
                        Reach::Thunk => Reach::Nested,
                        Reach::Head { .. } | Reach::Domain | Reach::Nested | Reach::Term => reach,
                    };
                    pending.push((AnyNode::ValueType(result), inner));
                },
                Some(&CompType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), term(reach)));
                },
                // The lazy product is a field-local former, so a self
                // occurrence in either component is nested.
                Some(&CompType::With(left, right)) => {
                    pending.push((AnyNode::CompType(left), nest(reach)));
                    pending.push((AnyNode::CompType(right), nest(reach)));
                },
                None => {},
            },
            AnyNode::Value(id) => match arena.value(id) {
                Some(&Value::Constant(index)) => {
                    if index >= block.end {
                        return Err(index);
                    }
                    if block.membership(index) == Membership::Family {
                        worst = worst.max(found(term(reach), Uniformity::NonUniform));
                    }
                    // A definition of the block is read through: what its
                    // body names, the field names where it names the
                    // definition (#602).
                    else if let Some(&(_, body)) =
                        definitions.iter().find(|&&(defined, _)| defined == index)
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
                Some(
                    &Value::SessionPath {
                        path_type,
                        payload_paths,
                        ..
                    }
                    | &Value::SessionFlow {
                        flow_type: path_type,
                        payload_paths,
                        ..
                    },
                ) => {
                    pending.push((AnyNode::ValueType(path_type), reach));
                    pending.push((AnyNode::Value(payload_paths), reach));
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
                Some(&Value::ForwardFlow {
                    flow_type,
                    translator,
                    ref outputs,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(flow_type), reach));
                    pending.push((AnyNode::Value(translator), reach));
                    pending.extend(
                        outputs
                            .iter()
                            .map(|&output| (AnyNode::Value(output), reach)),
                    );
                },
                Some(&Value::FunctionFlow {
                    flow_type,
                    domain,
                    codomain,
                }) => {
                    pending.push((AnyNode::ValueType(flow_type), reach));
                    pending.push((AnyNode::Value(domain), reach));
                    pending.push((AnyNode::Value(codomain), reach));
                },
                Some(
                    &(Value::PathProduct(first, second)
                    | Value::FlowProduct(first, second)
                    | Value::ListCons(first, second)
                    | Value::StaticApplication(first, second)
                    | Value::Then { first, second, .. }),
                ) => {
                    pending.push((AnyNode::Value(first), reach));
                    pending.push((AnyNode::Value(second), reach));
                },
                Some(&Value::Tuple(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| (AnyNode::Value(component), reach)),
                    );
                },
                Some(
                    &(Value::PathRefl(body)
                    | Value::Here { point: body, .. }
                    | Value::Stay { point: body, .. }
                    | Value::Injection(_, body)
                    | Value::Lift { body, .. }),
                ) => {
                    pending.push((AnyNode::Value(body), reach));
                },
                Some(
                    &Value::Higher {
                        evidence: ref values,
                        ..
                    }
                    | &Value::QuantifiedEvaluation {
                        children: ref values,
                        ..
                    },
                ) => {
                    pending.extend(values.iter().map(|&layer| (AnyNode::Value(layer), reach)));
                },
                Some(&Value::HigherEvaluation { ref components, .. }) => {
                    pending.extend(components.iter().flat_map(|component| {
                        [component.left, component.right, component.evidence]
                            .map(|child| (AnyNode::Value(child), reach))
                    }));
                },
                Some(&(Value::Thunk(body) | Value::Returned(body))) => {
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
                Some(&(Value::Variable(_) | Value::Literal(_) | Value::ListNil)) | None => {},
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
                Some(&Computation::SigmaSplit {
                    scrutinee,
                    motive,
                    body,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), reach));
                    pending.push((AnyNode::CompType(motive), reach));
                    pending.push((AnyNode::Computation(body), reach));
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
                    | Computation::Project(_, body)),
                ) => {
                    pending.push((AnyNode::Computation(body), reach));
                },
                Some(&Computation::Application(head, argument)) => {
                    pending.push((AnyNode::Computation(head), reach));
                    pending.push((AnyNode::Value(argument), reach));
                },
                Some(&(Computation::Bind(bound, body) | Computation::With(bound, body))) => {
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
                    pending.push((AnyNode::ValueType(motive), reach));
                    pending.push((AnyNode::Value(path), reach));
                    pending.push((AnyNode::Value(value), reach));
                },
                Some(
                    &(Computation::TelescopeTransport {
                        motive,
                        path,
                        start,
                        over,
                        value,
                    }
                    | Computation::TelescopeRide {
                        motive,
                        flow: path,
                        start,
                        over,
                        value,
                    }),
                ) => {
                    pending.push((AnyNode::CompType(motive), reach));
                    pending.extend(
                        [path, start, over, value].map(|child| (AnyNode::Value(child), reach)),
                    );
                },
                Some(&Computation::RelatedApplication {
                    path,
                    left,
                    right,
                    evidence,
                    body,
                }) => {
                    pending.extend(
                        [path, left, right, evidence].map(|child| (AnyNode::Value(child), reach)),
                    );
                    pending.push((AnyNode::Computation(body), reach));
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
                None => {},
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
) -> Result<(), KernelError>
{
    match finding {
        Finding::Admitted => Ok(()),
        Finding::NonUniform => Err(KernelError::NonUniformOccurrence(site)),
        Finding::Nested => Err(KernelError::NestedOccurrence(site)),
        Finding::Index => Err(KernelError::IndexOccurrence(site)),
        Finding::Negative => Err(KernelError::NegativeOccurrence(site)),
    }
}

/// Refuse every occurrence of a family of `block` in a data declaration
/// outside the two admitted field forms, and every reference past the block.
///
/// # Specification
/// - requires: `block` holds the admission position the declaration takes among
///   its families, `definitions` the bodies of its definitions by position,
///   `parameters` its telescope and `constructors` its field table scoped under
///   that telescope.
/// - ensures: success exactly when no parameter names a family of the block,
///   every field names one only directly or as a thunked function's codomain
///   whose domains do not name it, always at the parameter variables in order,
///   a definition of the block counting as the types its body quotes, and
///   nothing names a position past the block.
/// - provides: the strict-positivity and head-uniformity judgement the
///   formation of a recursive block rests on; it runs before any field forms.
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
///   admitted; a `T → A` field domain, a non-uniform head, a later reference, a
///   nested and an index occurrence are each refused by name at their site; a
///   universe naming its decoder is admitted with the decoder in its block; a
///   family named under a domain through a definition of its block is refused
///   as one named there directly.
/// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted`
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name`
/// - witness: `recursive_data::recursive_data::a_mutual_block_is_admitted`
/// - witness: `recursive_data::recursive_data::a_definition_of_the_block_is_read_through_602`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(
    KernelError::CrossBlockReference { .. }
    | KernelError::NegativeOccurrence(_)
    | KernelError::IndexOccurrence(_)
    | KernelError::NestedOccurrence(_)
    | KernelError::NonUniformOccurrence(_))))]
pub(super) fn occurrences(
    arena: &TermArena,
    block: Block,
    definitions: &[(ConstantIndex, ValueId)],
    parameters: &[ValueTypeId],
    constructors: &[Vec<ValueTypeId>],
) -> Result<(), KernelError>
{
    for (index, &parameter) in parameters.iter().enumerate() {
        let site = OccurrenceSite::Parameter(ParameterPosition::from(index));
        let finding = worst(
            arena,
            block,
            definitions,
            Telescope(index).into(),
            parameter,
            Reach::Term,
        )
        .map_err(|later| KernelError::CrossBlockReference { site, index: later })?;
        if finding != Finding::Admitted {
            return Err(KernelError::IndexOccurrence(site));
        }
    }
    for (tag, fields) in constructors.iter().enumerate() {
        let mut earlier = BinderDepth::NONE;
        for (field, &root) in fields.iter().enumerate() {
            let site = OccurrenceSite::Field {
                tag: ConstructorTag::from(tag),
                field: FieldPosition::from(field),
            };
            let scope = Scope {
                telescope: Telescope(parameters.len()),
                earlier,
            };
            let finding = worst(arena, block, definitions, scope, root, Reach::Head {
                depth: BinderDepth::NONE,
                site: HeadSite::Field,
            })
            .map_err(|later| KernelError::CrossBlockReference { site, index: later })?;
            refusal(finding, site)?;
            earlier = earlier.deeper();
        }
    }
    Ok(())
}

/// The position past the furthest one the data declaration at `position`
/// names: the end of the block its fields reach.
///
/// # Specification
/// - requires: `position` is the admission position the declaration takes.
/// - ensures: one past `position` when nothing in `parameters` or
///   `constructors` names a later position; otherwise one past the furthest
///   later position a parameter or a field names.
/// - provides: how a block is measured rather than declared, by the walk the
///   checker measures it by.
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
/// - witness: `recursive_data::recursive_data::a_mutual_block_is_admitted`
#[spec(ensures: |ret| ret > position)]
pub fn reach(
    arena: &TermArena,
    position: ConstantIndex,
    parameters: &[ValueTypeId],
    constructors: &[Vec<ValueTypeId>],
) -> ConstantIndex
{
    let mut block = Block::lone(position);
    for (index, &parameter) in parameters.iter().enumerate() {
        while let Err(later) = worst(
            arena,
            block,
            &[],
            Telescope(index).into(),
            parameter,
            Reach::Term,
        ) {
            block.end = ConstantIndex::from(usize::from(later).saturating_add(1));
        }
    }
    for fields in constructors {
        let mut earlier = BinderDepth::NONE;
        for &root in fields {
            let scope = Scope {
                telescope: Telescope(parameters.len()),
                earlier,
            };
            let start = Reach::Head {
                depth: BinderDepth::NONE,
                site: HeadSite::Field,
            };
            while let Err(later) = worst(arena, block, &[], scope, root, start) {
                block.end = ConstantIndex::from(usize::from(later).saturating_add(1));
            }
            earlier = earlier.deeper();
        }
    }
    block.end
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::TermArena;

    use super::Block;
    use super::Finding;
    use super::HeadSite;
    use super::Reach;
    use super::Telescope;
    use super::worst;
    use crate::rewrite::BinderDepth;

    /// A field's own type, where the walk starts a field.
    const FIELD: Reach = Reach::Head {
        depth: BinderDepth::NONE,
        site: HeadSite::Field,
    };

    #[test]
    fn a_named_position_is_read_against_the_declaration_s_own()
    {
        let position = ConstantIndex::from(1_usize);
        for (name, expected, what) in [
            (
                0_usize,
                Ok(Finding::Admitted),
                "an earlier position is the admitted prefix",
            ),
            (
                1_usize,
                Ok(Finding::Index),
                "the own position inside a term is an index",
            ),
            (
                2_usize,
                Err(ConstantIndex::from(2_usize)),
                "a later position is outside the block",
            ),
        ] {
            let mut arena = TermArena::new();
            let named = ConstantIndex::from(name);
            let atom = arena.value_type_abstract(named);
            assert_eq!(
                worst(
                    &arena,
                    Block::lone(position),
                    &[],
                    Telescope(0).into(),
                    atom,
                    FIELD
                ),
                expected,
                "as an abstract type: {what}"
            );
            let constant = arena.value_constant(named);
            let element = arena.value_type_element(constant, Level::zero());
            assert_eq!(
                worst(
                    &arena,
                    Block::lone(position),
                    &[],
                    Telescope(0).into(),
                    element,
                    FIELD
                ),
                expected,
                "as a constant: {what}"
            );
        }
    }
}
