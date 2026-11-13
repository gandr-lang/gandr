//! The records of the derived identity operations that the lowering's context
//! holds.
//!
//! The classification reads `back`, `cong`, a composite and a dependent
//! transport into these records, with where each reads its motive. The mint
//! sweep reads them back, and `gandr-surface-lowering` names each one at its
//! old path.

use anodized::spec;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::compose::Composite;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::arity::Dependent;
use super::arity::Place;
use super::native::Answer;
use crate::by_form::FormStretch;
use crate::resolve::Frame;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;

/// A derived operation's written operands.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each operand is the syntax node it was written as.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — each operation transports along its own path.
/// - witness: `gandr-surface-lowering::lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Derivation
{
    /// `Path.back(path)`.
    Back
    {
        /// The path reversed.
        path: NodeIndex,
    },
    /// `Path.ap(function, path)`.
    Cong
    {
        /// The map applied along the path.
        function: NodeIndex,
        /// The path mapped.
        path: NodeIndex,
    },
    /// `compose[n, k](chain(m), (c₁, …, cₘ))`.
    Compose
    {
        /// The stratum and the chain.
        composite: Composite,
        /// The cells in vertex order, in the lowerer's operand store.
        cells: FormStretch,
    },
}

/// A derived operation as the classification planned it: its operands, how
/// its motive is read, and the frame it stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the stance is a written path type, under a returner or not, or
///   the synthesis from the operands `Lowerer::derive` admitted.
/// - executable: none — the plan holds no tree to check its stance against.
///
/// # Adequacy
/// - hypothesis: L3 — each operation's motive is read off its answer, or off
///   its operands where no answer is written.
/// - witness: `gandr-surface-lowering::lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Derived
{
    /// The operation and its operands.
    pub derivation: Derivation,
    /// Where the motive's carrier and fixed endpoint are read.
    pub stance: Stance,
    /// The frame the operation stands under.
    pub frame: Frame,
}

/// Where a derived operation reads its motive's carrier and fixed endpoint.
///
/// # Specification
/// - ensures: the path type the position answers, or the operands' own path
///   types.
/// - executable: none — a tag holds no tree to check its reading against.
///
/// # Adequacy
/// - hypothesis: L3 — an answered and a synthesised operation each mint their
///   own motive.
/// - witness: `gandr-surface-lowering::lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Stance
{
    /// The path type the position answers.
    Answered(Answer),
    /// The operands' path types, the position answering none, with what the
    /// classification read them off where their own form spells none.
    Synthesised(Synthesis, Typings),
}

/// What the paths of a synthesised derived operation read their types off.
///
/// A path reads its type off this record where its own form spells none.
/// `Lowerer::refuse_unsynthesised` reads the record. The plan keeps it,
/// because the mint sweep consumes the plans of the operands before it
/// reaches the operation.
///
/// # Specification
/// - ensures: the motive's path — `back`'s and `cong`'s path, `then`'s first —
///   and `then`'s second, each a parameter or a call, or nothing.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — an operation over a parameter and over a call each mint
///   their path type.
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Typings
{
    /// The motive's path.
    pub transported: Option<Typed>,
    /// `then`'s second path.
    pub onward: Option<Typed>,
}

/// What a synthesised derived operation reads besides its paths' types.
///
/// # Specification
/// - ensures: nothing for `back` and `then`; for `cong`, the written result
///   type of the function it maps by, or, for a parameter, its written type
///   until `Lowerer::refuse_unsynthesised` reads its arrow's codomain, and then
///   that codomain with the frame it is carried from; for a lambda, the lambda,
///   whose body's path type is its codomain.
/// - executable: none — a tag holds no tree to check its reading against.
///
/// # Adequacy
/// - hypothesis: L3 — `cong` reads its codomain off its function, the others
///   off their paths alone.
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Synthesis
{
    /// The paths' types alone: `back` and `then`.
    Paths,
    /// The function's result type as its definition writes it, read under
    /// `frame`: `cong`.
    Mapped
    {
        /// The result type.
        codomain: Codomain,
        /// The frame the result type is read under.
        frame: Frame,
    },
    /// A parameter's written type, the thunk of the arrow whose codomain
    /// `cong` reads once every node is classified.
    Thunked
    {
        /// The binder's written type.
        declared: NodeIndex,
    },
    /// A declaration's written signature, which states the map whose
    /// codomain `cong` reads once every node is classified, as it reads a
    /// function definition's result.
    Stated
    {
        /// The signature's written type.
        declared: NodeIndex,
    },
    /// The codomain of the arrow a parameter's written type thunks, read under
    /// `frame`, the frame the parameter's type is read under: `cong` at a
    /// bound map. Every binder of `frame` is in scope where the operation
    /// stands, so the codomain is carried there.
    Bound
    {
        /// The codomain.
        codomain: Codomain,
        /// The frame the parameter's type, and so the codomain, is read
        /// under.
        frame: Frame,
        /// The frame the map's use stands under in a type; none in a body.
        in_type: Option<Frame>,
    },
    /// A lambda `fun (q) { e }` over the path's points, its binder typed by
    /// the path's carrier: `cong` reads its codomain off the path type its
    /// body `e` synthesises under that binder.
    Lambda
    {
        /// The lambda's node.
        lambda: NodeIndex,
    },
}

/// Where a `cong` reads the type its function returns.
///
/// # Specification
/// - ensures: a computation type returns its returner's result; a value
///   function's codomain is that result itself, the box `A -> B` standing for
///   `+U (A -> -F B)`.
/// - executable: none — a tag holds no tree to check its reading against.
///
/// # Adequacy
/// - hypothesis: L3 — `cong` by a parameter stated as `+U (A -> -F B)` and as
///   `A -> B` reads the same carrier.
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
/// - witness: `gandr-surface-lowering::lower::identity::tests::cong_reads_a_map_stated_as_a_value_function_791`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Codomain
{
    /// A written computation type, `-F B`: a definition's result or a thunked
    /// arrow's codomain.
    Returner(NodeIndex),
    /// The codomain `B` of a box `A -> B`.
    Returned(NodeIndex),
}

impl Codomain
{
    /// The codomain's syntax node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(self) -> NodeIndex
    {
        match self {
            Self::Returner(node) | Self::Returned(node) => node,
        }
    }
}

/// What a derived operation's path operand reads its type off when its own
/// form spells none.
///
/// # Specification
/// - ensures: the node of the written type the path's type is read from.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter and a call each mint the path type they
///   state, and a reflexivity's point its binder's type.
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_reflexivity_composes_at_a_point_of_any_type_3834`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Typed
{
    /// A parameter, by its binder's written type: named in a body, or in a
    /// type under the frame it is read from.
    Parameter
    {
        /// The binder's written type.
        declared: NodeIndex,
        /// The binder, which a call's argument may type (#3921).
        binder: ScopeId,
        /// The frame a type naming the binder reads it under; nothing in a
        /// body.
        in_type: Option<Frame>,
    },
    /// A call, by its function's written result.
    Called(Callee),
    /// A reflexivity `Path.here(x)` at a binder, by the binder's written type
    /// `A`: the reflexivity stands at `Path[.A = A](x, x)`.
    Point
    {
        /// The binder's written type.
        declared: NodeIndex,
        /// The binder, which a call's argument may type (#3921).
        binder: ScopeId,
        /// The frame a type naming the binder reads it under; nothing in a
        /// body.
        in_type: Option<Frame>,
    },
}

impl Typed
{
    /// The written type's node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(self) -> NodeIndex
    {
        match self {
            Self::Parameter { declared, .. } | Self::Point { declared, .. } => declared,
            Self::Called(callee) => callee.result,
        }
    }
}

/// A call whose function writes its result: what the call's path type is
/// instantiated from.
///
/// # Specification
/// - ensures: the function's parameters, its arity, the parameter it stages
///   when it recurses, its written result and whether that is a returner, the
///   arguments the call applies, and whether it is a recursive call's descent.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a call of a definition, of a signature and a recursive
///   call each mint their result at their arguments.
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Callee
{
    /// The function's binders, in the lowerer's parameter store: a tail's
    /// parameters or a telescope's entries; none for a plain value function.
    pub parameters: FormStretch,
    /// How many arguments the function takes.
    pub arity: usize,
    /// The staged parameter's position, when a recursive tail binds its own
    /// name between that parameter and the ones before it.
    pub recursive: Option<usize>,
    /// The written result: a tail's computation type, or a signature's
    /// value type.
    pub result: NodeIndex,
    /// Whether the result is a computation type, a returner over the path.
    pub returned: bool,
    /// The arguments the call applies, in the lowerer's operand store: every
    /// one, or a descent's from the staged parameter's on.
    pub arguments: FormStretch,
    /// Whether the head is a recursive call's descent claim, which passes
    /// the parameters before the staged one as themselves.
    pub descends: bool,
}

/// A dependent transport's written operands and the frame it stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each operand is the syntax node it was written as.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — each operand reaches its own slot of the transport.
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Transported
{
    /// The motive, written as a telescope.
    pub motive: NodeIndex,
    /// The path transported along.
    pub path: NodeIndex,
    /// The family element at the path's source.
    pub start: NodeIndex,
    /// The identity over the path.
    pub over: NodeIndex,
    /// The value transported.
    pub value: NodeIndex,
    /// The frame the transport stands under.
    pub frame: Frame,
}

/// The path type a derived operation minted at: its carrier and its two
/// endpoints, read where the operation stands.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the operation's transport returns an element of `Path[.A =
///   carrier]( left, right)`.
/// - executable: none — the ids hold no arena to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a synthesised operation over another reads the inner
///   one's path type.
/// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Identity
{
    /// The path's carrier.
    pub carrier: ValueTypeId,
    /// The path's left endpoint.
    pub left: ValueId,
    /// The path's right endpoint.
    pub right: ValueId,
}

/// The inverse's spelling: of a path, and of a loop where a word's letter is
/// written.
pub const BACK: &str = "back";

/// The record a relation between types abbreviates, or one of the records
/// nested in it, as a pattern splits it: its labels in written order and
/// whether each link binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Layout
{
    /// `A ≅ B`: `#{into, from, sect, retr}`.
    Isomorphism,
    /// `A ≃ B`: `#{into, linv, rinv}`, `linv` and `rinv` records of their own.
    Equivalence,
    /// The equivalence's left inverse `linv`: `#{from, sect}`.
    LeftInverse,
    /// The equivalence's right inverse `rinv`: `#{from, retr}`.
    RightInverse,
}

impl Layout
{
    /// The record's labels, in written order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn fields(self) -> impl ExactSizeIterator<Item = SurfaceName<'static>>
    {
        let labels: &'static [&'static str] = match self {
            Self::Isomorphism => &["into", "from", "sect", "retr"],
            Self::Equivalence => &["into", "linv", "rinv"],
            Self::LeftInverse => &["from", "sect"],
            Self::RightInverse => &["from", "retr"],
        };
        labels.iter().map(|&label| SurfaceName::from(label))
    }

    /// Whether each field but the last binds a later one: every map does,
    /// a round trip and an inverse do not.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn links(self) -> &'static [Dependent]
    {
        match self {
            Self::Isomorphism => &[Dependent(true), Dependent(true), Dependent(false)],
            Self::Equivalence => &[Dependent(true), Dependent(false)],
            Self::LeftInverse | Self::RightInverse => &[Dependent(true)],
        }
    }

    /// The record nested at `place`, when the field there is one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the equivalence's left inverse at its second field and its
    ///   right inverse at its third; the other-former absence for every other
    ///   field.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pattern at an equivalence splits both inverses.
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_pattern_at_a_relation_splits_its_record`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || self == Self::Equivalence)]
    #[inline]
    pub fn inner(
        self,
        place: Place,
    ) -> Maybe<Self, related::Absent>
    {
        match (self, place.0) {
            (Self::Equivalence, 1_usize) => Maybe::Present(Self::LeftInverse),
            (Self::Equivalence, 2_usize) => Maybe::Present(Self::RightInverse),
            _ => Maybe::Absent(related::Absent::Otherwise),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a type states no relation's record.
    pub mod related {
        /// The type is no equivalence or quasi-inverse.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The type is planned as another former, or as a flow.
            Otherwise,
        }
    }
}
