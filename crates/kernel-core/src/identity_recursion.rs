//! Element identity and bridges as a structural fold of quoted codes.
//!
//! The fold builds an indexed relation program, not an equality decision.
//! Its interpreter retains neutral fibres. Identity adds derived reflexivity
//! and transport; bridge families carry neither obligation. Universe identity
//! consumes `path_universe`; universe bridges classify these relation programs.
//!
//! Handles refer to the original arena contents: callers must retain their
//! code and value nodes, without truncating and reusing their addresses.
//! No relation, fibre or identity handle admits a declaration.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::check::check_closed_value;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::error::KernelError;
use crate::path_universe;
use crate::replay::ReplayBudget;

mod evaluation;
mod evidence;
#[cfg(test)]
mod tests;

pub use evaluation::Fiber;
pub use evaluation::FiberId;
pub use evaluation::Fibers;
pub use evaluation::Index;
pub use evaluation::IndexId;
pub use evidence::Identity;
pub use evidence::Transport;

/// The fibrant or non-fibrant reading of the same structural fold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode
{
    /// Element identity, with reflexivity and transport operations.
    Identity,
    /// A relation, without invertibility or transport obligations.
    Bridge,
}

/// A quoted element code, or the classifier of the closed codes themselves.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Domain
{
    /// Interpret elements of this quoted first-order type.
    Elements(ValueId),
    /// Interpret the closed code universe; this is not a nested universe code.
    Codes,
}

/// A local relation-program address, never an admission capability.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RelationId(usize);

/// A relation combinator; children are local addresses in a flat program.
#[derive(Clone, Copy, Debug)]
enum Clause
{
    /// The constantly inhabited fibre.
    Unit,
    /// The constantly empty fibre.
    Empty,
    /// Discrete equality of canonical base data, residual on neutral inputs.
    Discrete,
    /// Related product coordinates, independently.
    Product(RelationId, RelationId),
    /// Matching injections recurse; different injections have empty fibre.
    Sum(RelationId, RelationId),
    /// Split the left endpoint; both branches share the right endpoint type.
    CaseLeft(RelationId, RelationId),
    /// Split the right endpoint; both branches share the left endpoint type.
    CaseRight(RelationId, RelationId),
}

/// One typed relation combinator.
#[derive(Clone, Copy, Debug)]
struct Node
{
    /// Type of its left index.
    source: ValueTypeId,
    /// Type of its right index.
    target: ValueTypeId,
    /// The fibre computation.
    clause: Clause,
}

/// A finite, arena-relative indexed family, independent of its inhabitants.
///
/// # Specification
/// - provides: a relation between two closed first-order types; construction
///   owns the flat program, and operations recheck arena-relative endpoints.
/// - ensures: identity programs arise only from the code fold. Bridge programs
///   can additionally be constant or case-indexed relations.
///
/// # Adequacy
/// - hypothesis: L3 — a heterogeneous case-indexed bridge separates arbitrary
///   relations from equivalences and from structural equality of endpoint
///   codes.
/// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
#[derive(Clone, Debug)]
pub struct Relation
{
    /// Whether reflexivity and transport are available.
    mode: Mode,
    /// Constructor-ordered program storage.
    nodes: Vec<Node>,
    /// The final combinator.
    root: RelationId,
}

/// The result of the one code recursion, including its universe clause.
#[derive(Clone, Debug)]
pub enum Interpretation
{
    /// An indexed family over the elements of a quoted code.
    Elements(Relation),
    /// Universe identity is precisely the existing certified-equivalence
    /// former.
    UniverseIdentity,
    /// Universe bridges classify relation families, with no equality
    /// reflection.
    UniverseBridge,
}

/// A failure to form or use an experimental relation.
#[derive(Debug)]
pub enum RelationError
{
    /// An arena reference is unreadable.
    Arena,
    /// A code is not a quote.
    UnsupportedCode(ValueId),
    /// A former is outside the first-order fragment.
    UnsupportedType(ValueTypeId),
    /// A sealed type exposes no element relation or its structure.
    AbstractInterface(ValueTypeId),
    /// Ordinary kernel formation or checking failed.
    Typing(Box<KernelError>),
    /// A universe path failed its existing formation judgement.
    Path(Box<path_universe::PathError>),
    /// Composition endpoints do not agree definitionally.
    Boundary,
    /// A bridge cannot supply fibrant operations.
    NonFibrant,
    /// A neutral fibre has no native closed type reduct yet.
    NeutralFiber,
    /// A supplied proof does not inhabit its computed fibre.
    Evidence,
    /// The requested operation uses the wrong universe interpretation.
    Classifier,
}

impl fmt::Display for RelationError
{
    /// Show the exact experimental failure class.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Arena => f.write_str("unreadable relation arena reference"),
            | Self::UnsupportedCode(_) => f.write_str("relation domain is not a quoted code"),
            | Self::UnsupportedType(_) => {
                f.write_str("relation code is outside the first-order fragment")
            },
            | Self::AbstractInterface(_) => {
                f.write_str("sealed type has no element-relation interface")
            },
            | Self::Typing(ref error) => write!(f, "relation typing failed: {error}"),
            | Self::Path(ref error) => write!(f, "universe identity failed: {error}"),
            | Self::Boundary => f.write_str("relation indices do not match"),
            | Self::NonFibrant => f.write_str("bridge has no identity transport structure"),
            | Self::NeutralFiber => f.write_str("relation fibre is neutral"),
            | Self::Evidence => f.write_str("relation fibre has no constructed evidence"),
            | Self::Classifier => f.write_str("wrong relation classifier"),
        }
    }
}

impl core::error::Error for RelationError
{
}

/// Define identity and bridges together by one postorder recursion over codes.
///
/// # Specification
/// - requires: codes and their types belong to `arena`.
/// - ensures: Unit, Base, Sum and Product each contribute one relation clause,
///   in either mode; Abstract refuses before nominal comparison. The Codes
///   clause selects certified paths or indexed relation families.
/// - provides: a flat iterative fold; it never compares endpoint elements.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `AbstractInterface`, `Arena`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — both modes share every constructor boundary; nested
///   sealed types refuse even when both requested endpoints would be identical.
/// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
/// - witness: `identity_recursion::tests::abstract_is_an_interface_obstruction`
#[inline]
pub fn interpret(
    arena: &TermArena,
    mode: Mode,
    domain: Domain,
) -> Result<Interpretation, RelationError>
{
    let code = match domain {
        | Domain::Codes => {
            return Ok(match mode {
                | Mode::Identity => Interpretation::UniverseIdentity,
                | Mode::Bridge => Interpretation::UniverseBridge,
            });
        },
        | Domain::Elements(code) => code,
    };
    let root = quoted(arena, code)?;
    let mut pending = Vec::from([(root, false)]);
    let mut formed = BTreeMap::new();
    let mut nodes = Vec::new();
    while let Some((ty, expanded)) = pending.pop() {
        if formed.contains_key(&ty) {
            continue;
        }
        let node = arena.value_type(ty).ok_or(RelationError::Arena)?;
        let clause = match *node {
            | ValueType::Unit => Clause::Unit,

            | ValueType::Base(_) => Clause::Discrete,
            | ValueType::Sum(left, right) | ValueType::Product(left, right) => {
                if !expanded {
                    pending.push((ty, true));
                    pending.push((right, false));
                    pending.push((left, false));
                    continue;
                }
                let left = *formed.get(&left).ok_or(RelationError::Arena)?;
                let right = *formed.get(&right).ok_or(RelationError::Arena)?;
                match *node {
                    | ValueType::Sum(..) => Clause::Sum(left, right),
                    | _ => Clause::Product(left, right),
                }
            },
            | ValueType::Abstract(_) => return Err(RelationError::AbstractInterface(ty)),
            | _ => return Err(RelationError::UnsupportedType(ty)),
        };
        let id = RelationId(nodes.len());
        nodes.push(Node {
            source: ty,
            target: ty,
            clause,
        });
        formed.insert(ty, id);
    }
    let root = *formed.get(&root).ok_or(RelationError::Arena)?;
    Ok(Interpretation::Elements(Relation { mode, nodes, root }))
}

/// Decode a quote without guessing at a neutral code.
///
/// # Specification
/// - ensures: returns the quoted type, or `UnsupportedCode`.
/// - fails: `UnsupportedCode` for every non-quote or unreadable value.
/// - panics: none.
///
/// # Errors
/// `RelationError::UnsupportedCode`.
///
/// # Adequacy
/// - hypothesis: L3 — a value variable is not mistaken for a closed code.
/// - witness: `identity_recursion::tests::abstract_is_an_interface_obstruction`
fn quoted(
    arena: &TermArena,
    code: ValueId,
) -> Result<ValueTypeId, RelationError>
{
    match arena.value(code) {
        | Some(&Value::Quote(ty)) => Ok(ty),
        | _ => Err(RelationError::UnsupportedCode(code)),
    }
}

impl Interpretation
{
    /// Extract the element-family result of the fold.
    ///
    /// # Specification
    /// - ensures: returns the element relation without reinterpreting any code.
    /// - fails: `Classifier` for either universe clause.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Classifier`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe classifier cannot masquerade as an element
    ///   family.
    /// - witness: `identity_recursion::tests::universe_identity_consumes_path_formation`
    #[inline]
    pub fn elements(self) -> Result<Relation, RelationError>
    {
        match self {
            | Self::Elements(relation) => Ok(relation),
            | Self::UniverseIdentity | Self::UniverseBridge => Err(RelationError::Classifier),
        }
    }

    /// Form universe identity by the existing certified-equivalence judgement.
    ///
    /// # Specification
    /// - ensures: returns exactly the classifier checked by
    ///   `path_universe::form`.
    /// - fails: `Classifier` outside identity at Codes; `Path` on invalid
    ///   evidence.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid reflexivity forms; malformed equivalences
    ///   refuse through the existing checker, rather than a second identity
    ///   definition.
    /// - witness: `identity_recursion::tests::universe_identity_consumes_path_formation`
    #[inline]
    pub fn path(
        &self,
        arena: &mut TermArena,
        paths: &path_universe::Paths,
        path: path_universe::PathId,
        budget: ReplayBudget,
    ) -> Result<path_universe::PathType, RelationError>
    {
        if !matches!(self, Self::UniverseIdentity) {
            return Err(RelationError::Classifier);
        }
        path_universe::form(arena, paths, path, budget)
            .map_err(|error| RelationError::Path(Box::new(error)))
    }

    /// Check a relation as a bridge between the two quoted endpoint codes.
    ///
    /// # Specification
    /// - ensures: both endpoints are closed first-order codes and match the
    ///   relation's index types; no equivalence or strict element equality is
    ///   owed.
    /// - fails: `Classifier`, a code-fold error, or `Boundary` for wrong
    ///   indices.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Unit-to-Bool accepts a dependent relation, and
    ///   rejects a family with a different right index type.
    /// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
    #[inline]
    pub fn bridge(
        &self,
        arena: &TermArena,
        source: ValueId,
        target: ValueId,
        family: &Relation,
    ) -> Result<(), RelationError>
    {
        if !matches!(self, Self::UniverseBridge) {
            return Err(RelationError::Classifier);
        }
        let source = interpret(arena, Mode::Bridge, Domain::Elements(source))?;
        let source = source.elements()?;
        let target = interpret(arena, Mode::Bridge, Domain::Elements(target))?;
        let target = target.elements()?;
        let source = source.node(source.root)?;
        let source = source.source;
        let target = target.node(target.root)?;
        let target = target.source;
        let root = family.node(family.root)?;
        same_type(arena, source, root.source)?;
        same_type(arena, target, root.target)
    }
}

impl Relation
{
    /// The mode of the program.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn mode(&self) -> Mode
    {
        self.mode
    }

    /// Resolve a local program address.
    ///
    /// # Specification
    /// - ensures: returns the requested combinator or `Arena`.
    /// - fails: `Arena` for an unresolved address.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested product and sum programs preserve child
    ///   boundaries.
    /// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
    fn node(
        &self,
        id: RelationId,
    ) -> Result<Node, RelationError>
    {
        self.nodes.get(id.0).copied().ok_or(RelationError::Arena)
    }

    /// A constant Unit or Empty bridge over two independently checked codes.
    ///
    /// # Specification
    /// - ensures: constructs the selected constant family without identifying
    ///   endpoint codes or elements. `inhabited` selects Unit versus Empty.
    /// - fails: any code-fold error.
    /// - panics: none.
    ///
    /// # Errors
    /// `UnsupportedCode`, `UnsupportedType`, `AbstractInterface`, `Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both constant fibres retain heterogeneous indices.
    /// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
    #[inline]
    pub fn constant(
        arena: &TermArena,
        source: ValueId,
        target: ValueId,
        inhabited: Inhabitation,
    ) -> Result<Self, RelationError>
    {
        let source = interpret(arena, Mode::Bridge, Domain::Elements(source))?;
        let source = source.elements()?;
        let target = interpret(arena, Mode::Bridge, Domain::Elements(target))?;
        let target = target.elements()?;
        let source = source.node(source.root)?;
        let source = source.source;
        let target = target.node(target.root)?;
        let target = target.source;
        let clause = match inhabited {
            | Inhabitation::Unit => Clause::Unit,
            | Inhabitation::Empty => Clause::Empty,
        };
        Ok(Self {
            mode: Mode::Bridge,
            nodes: Vec::from([Node {
                source,
                target,
                clause,
            }]),
            root: RelationId(0),
        })
    }

    /// Build a relation by case analysis on either index, consuming both
    /// branches.
    ///
    /// # Specification
    /// - ensures: branch domains become a sum on the selected index; the other
    ///   index is shared definitionally. The resulting family is non-fibrant.
    /// - fails: `Boundary` for incompatible shared index types; `Arena` for a
    ///   malformed local program.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a right-index case distinguishes both Bool
    ///   injections; the mirror left-index case retains its independent
    ///   argument.
    /// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
    #[inline]
    pub fn cases(
        arena: &mut TermArena,
        index: CaseIndex,
        mut left: Self,
        right: Self,
    ) -> Result<Self, RelationError>
    {
        let first = left.node(left.root)?;
        let second = right.node(right.root)?;
        let (source, target) = match index {
            | CaseIndex::Left => {
                same_type(arena, first.target, second.target)?;
                (
                    arena.value_type_sum(first.source, second.source),
                    first.target,
                )
            },
            | CaseIndex::Right => {
                same_type(arena, first.source, second.source)?;
                (
                    first.source,
                    arena.value_type_sum(first.target, second.target),
                )
            },
        };
        let offset = RelationOffset(left.nodes.len());
        let right_root = relocate(right.root, offset);
        for mut node in right.nodes {
            node.clause = match node.clause {
                | Clause::Product(a, b) => {
                    Clause::Product(relocate(a, offset), relocate(b, offset))
                },
                | Clause::Sum(a, b) => Clause::Sum(relocate(a, offset), relocate(b, offset)),
                | Clause::CaseLeft(a, b) => {
                    Clause::CaseLeft(relocate(a, offset), relocate(b, offset))
                },
                | Clause::CaseRight(a, b) => {
                    Clause::CaseRight(relocate(a, offset), relocate(b, offset))
                },
                | clause => clause,
            };
            left.nodes.push(node);
        }
        let clause = match index {
            | CaseIndex::Left => Clause::CaseLeft(left.root, right_root),
            | CaseIndex::Right => Clause::CaseRight(left.root, right_root),
        };
        left.root = RelationId(left.nodes.len());
        left.nodes.push(Node {
            source,
            target,
            clause,
        });
        left.mode = Mode::Bridge;
        Ok(left)
    }
}

/// The two constant first-order relation fibres.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Inhabitation
{
    /// The unit type.
    Unit,
    /// The empty type.
    Empty,
}

/// Which argument a relation case splits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CaseIndex
{
    /// The source index.
    Left,
    /// The target index.
    Right,
}

/// A relocation offset within an owned relation program.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct RelationOffset(usize);

/// Shift an address when moving a flat program into another allocation.
///
/// # Specification
/// trivial.
fn relocate(
    id: RelationId,
    offset: RelationOffset,
) -> RelationId
{
    RelationId(id.0.saturating_add(offset.0))
}

/// Require definitional agreement of index types; never element equality.
///
/// # Specification
/// - ensures: success only for structurally convertible kernel types.
/// - fails: `Boundary` otherwise.
/// - panics: none.
///
/// # Errors
/// `RelationError::Boundary`.
///
/// # Adequacy
/// - hypothesis: L3 — mismatched relation indices cannot classify at `Br_U`.
/// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
fn same_type(
    arena: &TermArena,
    left: ValueTypeId,
    right: ValueTypeId,
) -> Result<(), RelationError>
{
    match convertible_value_types(arena, left, right) {
        | Convertibility::Convertible => Ok(()),
        | Convertibility::Distinct => Err(RelationError::Boundary),
    }
}

/// Check an open value by closing its telescope with ordinary dependent arrows.
///
/// # Specification
/// - ensures: value and expected type check in `context`, ordered outermost
///   first; every domain is formed by the ordinary kernel. Temporary wrappers
///   are removed on both outcomes.
/// - fails: `Typing` with the ordinary kernel diagnostic.
/// - panics: none.
///
/// # Errors
/// `RelationError::Typing`.
///
/// # Adequacy
/// - hypothesis: L3 — open base variables check only at their declared types;
///   no synthetic variable can smuggle in an identity assumption.
/// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
fn check_value(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    value: ValueId,
    expected: ValueTypeId,
) -> Result<(), RelationError>
{
    let mark = arena.watermark();
    let mut body = arena.computation_return(value);
    let mut ty = arena.comp_type_returner(expected);
    for &domain in context.iter().rev() {
        body = arena.computation_lambda(body);
        ty = arena.comp_type_pi(domain, ty);
    }
    let value = arena.value_thunk(body);
    let expected = arena.value_type_thunk(ty);
    let result = check_closed_value(arena, value, expected)
        .map_err(|error| RelationError::Typing(Box::new(error)));
    arena.truncate_to(mark);
    result
}
