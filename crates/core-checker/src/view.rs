//! The fragment's reading of a type node: the formers the judgement has rules
//! for, and a refusal by name for every other.
//!
//! # One place decides the fragment's types
//!
//! The core vocabulary has more type formers than the judgement has rules for.
//! Formation, the shape a check rule demands of its expected type, the shape an
//! elimination demands of a synthesised type, conversion and the kernel
//! bridge's erasure all read a type node through the two views here, so the
//! fragment's boundary on the type side is decided once: a former outside it is
//! [`FragmentRefusal::OutOfFragment`] wherever it is met, and no rule sees it.
//!
//! # A view reads a node, and unfolds nothing
//!
//! A decode `El c` is viewed as it stands, its code and level exposed. Whether
//! the code is a constant whose body is a quote, so that the decode stands for
//! another type, is the judgement's question — it is answered through the
//! normaliser's conversion with a certificate — and never a view's.
//!
//! # The unknown type is a view of its own
//!
//! The unknown type a hole or a mark synthesises, and the decode of a code
//! that is itself a hole or a mark, are both viewed as
//! [`ValueTypeView::Unknown`] or [`CompTypeView::Unknown`]: a rule reading a
//! type through a view meets the unknown once, under one name, whichever
//! spelling stands in the arena.
//!
//! # A refusal only a view can give
//!
//! A view refuses for two reasons and no others, so its refusal is its own
//! two-variant type; the judgement and the bridge each convert it into their
//! own vocabulary, and neither handles a refusal a view cannot give.
//!
//! # The fragment
//!
//! The judgement admits integer and string atoms, unit, products, sums, native
//! Lists, nominal data, sealed abstract types, structural records, thunks,
//! effect-qualified returners, arrows, dependent arrows, static operators,
//! universes, raising type lifts and decodes, and effects and control.
//! Injection checks against its sum; case checks both payload-bound branches
//! against one expected computation type. Numeric atoms and literals, value
//! lifts, non-raising lifts, sort-parameter universes and top-level universes
//! are named `OutOfFragment` refusals.

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::hole::Knowledge;
use gandr_core_term::hole::comp_type_knowledge;
use gandr_core_term::hole::value_type_knowledge;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::GroundSort;

use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;

/// Why a type node has no view.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentRefusal
{
    /// The id names no node of the arena.
    DanglingNode
    {
        /// The id.
        node: CoreNode,
    },
    /// The node's former has no rule in the fragment.
    OutOfFragment
    {
        /// The node carrying the former.
        at: CoreNode,
        /// The former.
        former: UnadmittedFormer,
    },
}

impl From<FragmentRefusal> for CheckRefusal
{
    /// The judgement's refusal for a node its views cannot read.
    ///
    /// # Specification
    /// - ensures: each variant becomes the [`CheckRefusal`] variant of the same
    ///   name, with the same payload.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dangling value-type id and each rejected former are
    ///   observed as named checker refusals; this separates a lost node
    ///   identity or a fragment refusal misclassified as an engine fault.
    ///   Successful views are outside this conversion.
    /// - witness: `formation::tests::a_dangling_type_is_refused_as_a_fault`
    /// - witness: `formation::tests::unsupported_forms_have_nominal_kinds`
    #[spec(ensures: |ret| match refusal {
        | FragmentRefusal::DanglingNode { node } => ret == Self::DanglingNode { node },
        | FragmentRefusal::OutOfFragment { at, former } => ret == Self::OutOfFragment { at, former },
    })]
    #[inline]
    fn from(refusal: FragmentRefusal) -> Self
    {
        match refusal {
            | FragmentRefusal::DanglingNode { node } => Self::DanglingNode { node },
            | FragmentRefusal::OutOfFragment { at, former } => Self::OutOfFragment { at, former },
        }
    }
}

/// A value type the fragment admits, with its children.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueTypeView<'arena>
{
    /// A nominal identity applied to genuine value arguments.
    Data
    {
        /// The admission position defining the datatype.
        declaration: gandr_kernel_term::ConstantIndex,
        /// Arguments in telescope order.
        arguments: &'arena [ValueId],
    },
    /// Structural record fields in exact label order.
    Record(&'arena alloc::collections::BTreeMap<gandr_core_term::FieldLabel, ValueTypeId>),
    /// A stack consuming one computation type and delivering another.
    Stack
    {
        /// The type accepted by the stack.
        input: CompTypeId,
        /// The type delivered to its caller.
        output: CompTypeId,
    },
    /// A native universe-path classifier over two codes.
    PathUniverse(ValueId, ValueId),
    /// Element identity `Path(A, a, b)`: the paths from `a` to `b` in `A`.
    Path
    {
        /// The carrier `A`.
        carrier: ValueTypeId,
        /// The left endpoint.
        left: ValueId,
        /// The right endpoint.
        right: ValueId,
    },
    /// Directed identity `Flow(A, a, b)`: the forward-only flows from `a` to
    /// `b` in `A`.
    Flow
    {
        /// The carrier `A`.
        carrier: ValueTypeId,
        /// The source endpoint.
        source: ValueId,
        /// The target endpoint.
        target: ValueId,
    },
    /// `Run(s)`: the complete recorded runs of the session code `s`.
    Run(ValueId),
    /// A sum of its summands, in order; the empty sum is the empty type.
    Sum(&'arena [ValueTypeId]),
    /// Finite lists over one element type.
    List(ValueTypeId),
    /// The integer atom.
    Integer,
    /// The string atom.
    String,
    /// The unit type, the product of no components.
    Unit,
    /// The thunk type `U C` of the computation type held.
    Thunk(CompTypeId),
    /// The universe `Type[s, l]` of a ground sort.
    Universe
    {
        /// The family the universe classifies.
        sort: GroundSort,
        /// Its level.
        level: &'arena Level,
    },
    /// The lift of a value type into a higher universe.
    Lift
    {
        /// The type lifted.
        inner: ValueTypeId,
        /// The level it is lifted to.
        target: &'arena Level,
    },
    /// The value type a code denotes.
    Element
    {
        /// The code.
        code: ValueId,
        /// The level of the universe the code inhabits.
        target: &'arena Level,
    },
    /// The eager product `A₁ × … × Aₙ` of one or more value types, in order.
    Product(&'arena [ValueTypeId]),
    /// The static Pi: the classifier of a type operator from codes of its
    /// domain to codes of its codomain, which stands in the ambient context.
    StaticPi
    {
        /// The classifier of the operator's argument.
        domain: ValueTypeId,
        /// The classifier of what it builds.
        codomain: ValueTypeId,
    },
    /// A sealed abstract type: the atom declared at this admission position.
    Abstract(gandr_kernel_term::ConstantIndex),
    /// A capability `Cap E`: a hypothesis carrying the authority `E` for a
    /// region at a grade.
    Capability
    {
        /// The grant atoms.
        authority: &'arena gandr_core_term::effect::EffectRow,
        /// How often it may be exercised.
        grade: gandr_core_term::effect::capability::CapabilityGrade,
        /// How long it lives.
        region: gandr_core_term::effect::capability::Region,
    },
    /// A session type: the protocol state an endpoint is at, with its
    /// payloads.
    Session(&'arena gandr_core_term::session::SessionType),
    /// The unknown type: a hole's or a mark's, or the decode of one.
    Unknown,
}

/// A computation type the fragment admits, with its children.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompTypeView<'arena>
{
    /// A lazy pair of computations, selected by projection.
    With(CompTypeId, CompTypeId),
    /// The returner `F A` of the value type held.
    Returner
    {
        /// The value returned.
        result: ValueTypeId,
        /// The operations permitted while producing it.
        effects: &'arena gandr_core_term::effect::EffectRow,
    },
    /// The non-dependent arrow `A → C`: its codomain stands in the ambient
    /// context.
    Arrow
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain.
        codomain: CompTypeId,
    },
    /// The dependent arrow `Π (x : A). C`: its codomain is scoped under one
    /// binder of the domain.
    Pi
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain, under the binder.
        codomain: CompTypeId,
    },
    /// The computation type a code denotes.
    Element
    {
        /// The code.
        code: ValueId,
        /// The level of the universe the code inhabits.
        target: &'arena Level,
    },
    /// The unknown computation type: a hole's or a mark's, or the decode of
    /// one.
    Unknown,
}

/// Read a value-type node as the fragment admits it.
///
/// # Specification
/// - requires: nothing — a dangling id and a former outside the fragment are
///   both admissible input and both refused.
/// - ensures: the node's view when its former is the integer atom, the string
///   atom, the empty product (the unit type), a thunk type, a universe of a
///   ground sort, a lift, a decode, a product of one or more components, a sum
///   of any number of summands, a static Pi, a path type, a flow type, a run
///   type, a sealed atom, a session type or a capability; the children are the
///   node's own. The unknown type, and a decode whose code is a hole or a mark,
///   view as [`ValueTypeView::Unknown`].
/// - provides: the one decision of which value types the judgement and the
///   bridge reason about.
/// - fails: [`FragmentRefusal::DanglingNode`] when the id names no node of
///   `arena`; [`FragmentRefusal::OutOfFragment`], naming the former, for the
///   numeric atom and a universe over a sort parameter.
/// - panics: none.
///
/// # Errors
/// - [`FragmentRefusal::DanglingNode`] — the id does not resolve.
/// - [`FragmentRefusal::OutOfFragment`] — the former has no rule in the
///   fragment.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the per-former table, separated
///   by one node of every value-type former of the core vocabulary, each
///   asserted to view or to refuse with its exact former, plus a dangling id;
///   the unknown type and a decode of a hole against a decode of a variable
///   separate the two readings of a decode.
/// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::abstract_sort_raises_the_exact_variant`
/// - witness: `formation::tests::a_dangling_type_is_refused_as_a_fault`
/// - witness: `view::tests::products_and_sums_view_at_every_arity`
/// - witness: `view::tests::the_unknown_type_and_the_decode_of_a_hole_view_alike`
#[spec(ensures: |ret| match ret {
    | Ok(ValueTypeView::Data { declaration, arguments }) => matches!(arena.value_type(value_type), Some(ValueType::Data { declaration: actual, arguments: args }) if *actual == declaration && args == arguments),
    | Ok(ValueTypeView::Record(fields)) => matches!(arena.value_type(value_type), Some(ValueType::Record(actual)) if actual == fields),
    | Ok(ValueTypeView::Stack { input, output }) => matches!(arena.value_type(value_type), Some(ValueType::Stack { input: found_input, output: found_output }) if *found_input == input && *found_output == output),
    | Ok(ValueTypeView::Integer) => matches!(arena.value_type(value_type), Some(ValueType::Base(BaseType::Integer))),
    | Ok(ValueTypeView::String) => matches!(arena.value_type(value_type), Some(ValueType::Base(BaseType::String))),
    | Ok(ValueTypeView::Unit) => arena.value_type(value_type).is_some_and(|held| matches!(*held, ValueType::Product(ref parts) if parts.is_empty())),
    | Ok(ValueTypeView::Thunk(held)) => matches!(arena.value_type(value_type), Some(ValueType::Thunk(inner)) if *inner == held),
    | Ok(ValueTypeView::PathUniverse(first, second)) => matches!(arena.value_type(value_type), Some(ValueType::PathUniverse(left, right)) if *left == first && *right == second),
    | Ok(ValueTypeView::Path { carrier, left, right }) => matches!(arena.value_type(value_type), Some(&ValueType::Path { carrier: found, left: first, right: second }) if found == carrier && first == left && second == right),
    | Ok(ValueTypeView::Flow { carrier, source, target }) => matches!(arena.value_type(value_type), Some(&ValueType::Flow { carrier: found, source: first, target: second }) if found == carrier && first == source && second == target),
    | Ok(ValueTypeView::Run(session)) => matches!(arena.value_type(value_type), Some(&ValueType::Run(found)) if found == session),
    | Ok(ValueTypeView::Sum(summands)) => arena.value_type(value_type).is_some_and(|held| matches!(*held, ValueType::Sum(ref parts) if **parts == *summands)),
    | Ok(ValueTypeView::List(element)) => matches!(arena.value_type(value_type), Some(ValueType::List(found)) if *found == element),
    | Ok(ValueTypeView::Product(components)) => !components.is_empty() && arena.value_type(value_type).is_some_and(|held| matches!(*held, ValueType::Product(ref parts) if **parts == *components)),
    | Ok(ValueTypeView::Universe { sort, level }) => matches!(arena.value_type(value_type), Some(ValueType::Universe { sort: Sort::Ground(found), level: found_level }) if *found == sort && found_level == level),
    | Ok(ValueTypeView::Lift { inner, target }) => matches!(arena.value_type(value_type), Some(ValueType::Lift { inner: found, target: found_target }) if *found == inner && found_target == target),
    | Ok(ValueTypeView::Element { code, target }) => matches!(arena.value_type(value_type), Some(ValueType::Element { code: found, target: found_target }) if *found == code && found_target == target)
        && value_type_knowledge(arena, value_type) == Knowledge::Known,
    | Ok(ValueTypeView::StaticPi { domain, codomain }) => matches!(arena.value_type(value_type), Some(ValueType::StaticPi { domain: found_domain, codomain: found_codomain }) if *found_domain == domain && *found_codomain == codomain),
    | Ok(ValueTypeView::Abstract(atom)) => matches!(arena.value_type(value_type), Some(&ValueType::Abstract(found)) if found == atom),
    | Ok(ValueTypeView::Session(session)) => arena.value_type(value_type).is_some_and(|held| matches!(*held, ValueType::Session(ref found) if found == session)),
    | Ok(ValueTypeView::Capability { authority, grade, region }) => matches!(arena.value_type(value_type), Some(&ValueType::Capability { authority: ref found, grade: found_grade, region: found_region }) if found == authority && found_grade == grade && found_region == region),
    | Ok(ValueTypeView::Unknown) => value_type_knowledge(arena, value_type) == Knowledge::Unknown,
    | Err(FragmentRefusal::DanglingNode { node }) => arena.value_type(value_type).is_none() && node == CoreNode::Type(TypeNode::Value(value_type)),
    | Err(FragmentRefusal::OutOfFragment { at, former }) => at == CoreNode::Type(TypeNode::Value(value_type))
        && match (arena.value_type(value_type), former) {
            | (Some(&ValueType::Base(BaseType::Numeric)), UnadmittedFormer::NumericAtom)
            | (Some(&ValueType::Universe { sort: Sort::Parameter(_), .. }), UnadmittedFormer::SortParameter) => true,
            | _ => false,
        },
})]
pub fn value_type_view(
    arena: &CoreArena,
    value_type: ValueTypeId,
) -> Result<ValueTypeView<'_>, FragmentRefusal>
{
    let at = CoreNode::Type(TypeNode::Value(value_type));
    let Some(node) = arena.value_type(value_type)
    else {
        return Err(FragmentRefusal::DanglingNode { node: at });
    };
    let unadmitted = |former| FragmentRefusal::OutOfFragment { at, former };
    match *node {
        | ValueType::Data {
            declaration,
            ref arguments,
        } => Ok(ValueTypeView::Data {
            declaration,
            arguments,
        }),
        | ValueType::Record(ref fields) => Ok(ValueTypeView::Record(fields)),
        | ValueType::Stack { input, output } => Ok(ValueTypeView::Stack { input, output }),
        | ValueType::PathUniverse(source, target) => {
            Ok(ValueTypeView::PathUniverse(source, target))
        },
        | ValueType::Path {
            carrier,
            left,
            right,
        } => Ok(ValueTypeView::Path {
            carrier,
            left,
            right,
        }),
        | ValueType::Flow {
            carrier,
            source,
            target,
        } => Ok(ValueTypeView::Flow {
            carrier,
            source,
            target,
        }),
        | ValueType::Run(session) => Ok(ValueTypeView::Run(session)),
        | ValueType::Base(BaseType::Integer) => Ok(ValueTypeView::Integer),
        | ValueType::Base(BaseType::String) => Ok(ValueTypeView::String),
        | ValueType::Base(BaseType::Numeric) => Err(unadmitted(UnadmittedFormer::NumericAtom)),
        | ValueType::Thunk(body) => Ok(ValueTypeView::Thunk(body)),
        | ValueType::Product(ref parts) if parts.is_empty() => Ok(ValueTypeView::Unit),
        | ValueType::Product(ref parts) => Ok(ValueTypeView::Product(parts)),
        | ValueType::Sum(ref parts) => Ok(ValueTypeView::Sum(parts)),
        | ValueType::List(element) => Ok(ValueTypeView::List(element)),
        | ValueType::Universe {
            sort: Sort::Ground(sort),
            ref level,
        } => Ok(ValueTypeView::Universe { sort, level }),
        | ValueType::Universe {
            sort: Sort::Parameter(_),
            ..
        } => Err(unadmitted(UnadmittedFormer::SortParameter)),
        | ValueType::Lift { inner, ref target } => Ok(ValueTypeView::Lift { inner, target }),
        | ValueType::Element { code, ref target } => {
            match value_type_knowledge(arena, value_type) {
                | Knowledge::Known => Ok(ValueTypeView::Element { code, target }),
                | Knowledge::Unknown => Ok(ValueTypeView::Unknown),
            }
        },
        | ValueType::Abstract(atom) => Ok(ValueTypeView::Abstract(atom)),
        | ValueType::Session(ref session) => Ok(ValueTypeView::Session(session)),
        | ValueType::StaticPi { domain, codomain } => {
            Ok(ValueTypeView::StaticPi { domain, codomain })
        },
        | ValueType::Capability {
            ref authority,
            grade,
            region,
        } => Ok(ValueTypeView::Capability {
            authority,
            grade,
            region,
        }),
        | ValueType::Unknown => Ok(ValueTypeView::Unknown),
    }
}

/// Read a computation-type node as the fragment admits it.
///
/// # Specification
/// - requires: nothing — a dangling id is admissible input and refused.
/// - ensures: the node's view for every computation former: a returner, an
///   arrow, a dependent arrow and a decode; the children are the node's own.
///   The unknown type, and a decode whose code is a hole or a mark, view as
///   [`CompTypeView::Unknown`].
/// - provides: the one decision of which computation types the judgement and
///   the bridge reason about.
/// - fails: [`FragmentRefusal::DanglingNode`] when the id names no node of
///   `arena`.
/// - panics: none.
///
/// # Errors
/// - [`FragmentRefusal::DanglingNode`] — the id does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the five-former table, separated
///   by one node of each former viewed with its own children, and the unknown
///   type against a decode of a hole and a decode of a variable.
/// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::the_dependent_arrow_forms_at_the_join_of_its_levels`
/// - witness: `view::tests::both_views_refuse_ids_missing_from_their_arena`
/// - witness: `view::tests::the_unknown_type_and_the_decode_of_a_hole_view_alike`
#[spec(ensures: |ret| match (arena.comp_type(comp_type), ret) {
    | (Some(&CompType::With(first, second)), Ok(CompTypeView::With(left, right))) => first == left && second == right,
    | (Some(&CompType::Returner { result: inner, ref effects }), Ok(CompTypeView::Returner { result: held, effects: row })) => inner == held && effects == row,
    | (Some(&CompType::Arrow { domain, codomain }), Ok(CompTypeView::Arrow { domain: found_domain, codomain: found_codomain }))
    | (Some(&CompType::Pi { domain, codomain }), Ok(CompTypeView::Pi { domain: found_domain, codomain: found_codomain })) => domain == found_domain && codomain == found_codomain,
    | (Some(&CompType::Element { code, ref target }), Ok(CompTypeView::Element { code: found, target: found_target })) => code == found && target == found_target
        && comp_type_knowledge(arena, comp_type) == Knowledge::Known,
    | (Some(&(CompType::Element { .. } | CompType::Unknown)), Ok(CompTypeView::Unknown)) => comp_type_knowledge(arena, comp_type) == Knowledge::Unknown,
    | (None, Err(FragmentRefusal::DanglingNode { node })) => node == CoreNode::Type(TypeNode::Computation(comp_type)),
    | _ => false,
})]
pub fn comp_type_view(
    arena: &CoreArena,
    comp_type: CompTypeId,
) -> Result<CompTypeView<'_>, FragmentRefusal>
{
    let at = CoreNode::Type(TypeNode::Computation(comp_type));
    let Some(node) = arena.comp_type(comp_type)
    else {
        return Err(FragmentRefusal::DanglingNode { node: at });
    };
    match *node {
        | CompType::With(first, second) => Ok(CompTypeView::With(first, second)),
        | CompType::Returner {
            result,
            ref effects,
        } => Ok(CompTypeView::Returner { result, effects }),
        | CompType::Arrow { domain, codomain } => Ok(CompTypeView::Arrow { domain, codomain }),
        | CompType::Pi { domain, codomain } => Ok(CompTypeView::Pi { domain, codomain }),
        | CompType::Element { code, ref target } => match comp_type_knowledge(arena, comp_type) {
            | Knowledge::Known => Ok(CompTypeView::Element { code, target }),
            | Knowledge::Unknown => Ok(CompTypeView::Unknown),
        },
        | CompType::Unknown => Ok(CompTypeView::Unknown),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_core_term::Zone;
    use gandr_core_term::hole::HoleId;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::DeBruijnIndex;

    use super::CompTypeView;
    use super::FragmentRefusal;
    use super::ValueTypeView;
    use super::comp_type_view;
    use super::value_type_view;
    use crate::refusal::CoreNode;
    use crate::refusal::TypeNode;

    #[test]
    fn the_unknown_type_and_the_decode_of_a_hole_view_alike()
    {
        let mut arena = CoreArena::new();
        let hole = arena.value_hole(HoleId::from(0_u32));
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let unknown = arena.value_type_unknown();
        let decoded_hole = arena.value_type_element(hole, Level::zero());
        let decoded_variable = arena.value_type_element(variable, Level::zero());
        let unknown_computation = arena.comp_type_unknown();
        let decoded_hole_computation = arena.comp_type_element(hole, Level::zero());
        let decoded_variable_computation = arena.comp_type_element(variable, Level::zero());
        assert_eq!(value_type_view(&arena, unknown), Ok(ValueTypeView::Unknown));
        assert_eq!(
            value_type_view(&arena, decoded_hole),
            Ok(ValueTypeView::Unknown),
            "the decode of a hole is the unknown type"
        );
        assert!(
            matches!(value_type_view(&arena, decoded_variable), Ok(ValueTypeView::Element { code, .. }) if code == variable),
            "the decode of a variable stays a decode"
        );
        assert_eq!(
            comp_type_view(&arena, unknown_computation),
            Ok(CompTypeView::Unknown)
        );
        assert_eq!(
            comp_type_view(&arena, decoded_hole_computation),
            Ok(CompTypeView::Unknown)
        );
        assert!(matches!(
            comp_type_view(&arena, decoded_variable_computation),
            Ok(CompTypeView::Element { code, .. }) if code == variable
        ));
    }

    #[test]
    fn both_views_refuse_ids_missing_from_their_arena()
    {
        let mut producer = CoreArena::new();
        let value_type = producer.value_type_unit();
        let comp_type = producer.comp_type_returner(value_type);
        let empty = CoreArena::new();
        assert_eq!(
            value_type_view(&empty, value_type),
            Err(FragmentRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(value_type)),
            })
        );
        assert_eq!(
            comp_type_view(&empty, comp_type),
            Err(FragmentRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Computation(comp_type)),
            })
        );
    }

    #[test]
    fn products_and_sums_view_at_every_arity()
    {
        let mut arena = CoreArena::new();
        let a = arena.value_type_unit();
        let b = arena.value_type_list(a);
        let c = arena.value_type_unknown();
        let unit = arena.value_type_product(&[]);
        let pair = arena.value_type_product(&[a, b]);
        let single = arena.value_type_product(&[a]);
        let triple = arena.value_type_product(&[a, b, c]);
        let either = arena.value_type_sum(&[b, a]);
        let empty = arena.value_type_sum(&[]);
        let three = arena.value_type_sum(&[a, b, c]);
        assert_eq!(value_type_view(&arena, unit), Ok(ValueTypeView::Unit));
        assert_eq!(
            value_type_view(&arena, pair),
            Ok(ValueTypeView::Product(&[a, b]))
        );
        assert_eq!(
            value_type_view(&arena, either),
            Ok(ValueTypeView::Sum(&[b, a])),
            "the summands keep their order"
        );
        assert_eq!(
            value_type_view(&arena, single),
            Ok(ValueTypeView::Product(&[a]))
        );
        assert_eq!(
            value_type_view(&arena, triple),
            Ok(ValueTypeView::Product(&[a, b, c]))
        );
        assert_eq!(
            value_type_view(&arena, empty),
            Ok(ValueTypeView::Sum(&[])),
            "the empty sum is the empty type"
        );
        assert_eq!(
            value_type_view(&arena, three),
            Ok(ValueTypeView::Sum(&[a, b, c]))
        );
    }
}
