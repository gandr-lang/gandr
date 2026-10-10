//! The walk from a source's nodes to one layout document.
//!
//! The walk drains an explicit task stack: visiting a node either finishes a
//! piece at once or schedules its children and the join that combines them,
//! and a join pops the finished pieces it needs. Nothing recurses, so a deep
//! type or value costs heap, never native stack.
//!
//! Every break point is a choice whose inline branch carries the exact bytes
//! the one-line spelling carries there, so the flattened image of a document
//! is its one-line spelling and a wide page selects it unchanged; under width
//! pressure the same document breaks, a continuation indented two columns.
//!
//! Before the walk builds anything, a scan over the same nodes collects the
//! names the term spells, so a dependent arrow's generated binder never reads
//! as a constant or an abstract type the term mentions. Both passes bound
//! their scheduled visits, including when the source changes between passes.

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_surface_layout::arena::DocId;
use gandr_surface_layout::arena::TextSource;
use gandr_surface_layout::build::DocBuilder;
use gandr_surface_layout::units::NestAmount;
use quenchant_shape::shape::Maybe;

use crate::DEPTH_LIMIT;
use crate::Fidelity;
use crate::ValueDepth;
use crate::error::PresentationError;
use crate::former::Former;
use crate::former::Name;
use crate::former::Source;

quenchant_shape::reason_enum! {
    /// Why a universe has no surface spelling.
    pub mod universe {
        /// The reason no spelling is written.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The universe's sort is a parameter, which has no spelling.
            ParameterSort,
            /// The level mentions a level variable, which has no spelling.
            LevelVariable,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a binder has no generated name.
    pub mod binder {
        /// The reason no name is generated.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The candidate names ran out.
            Exhausted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a scan collected no names.
    pub mod scan {
        /// The reason the scan stopped.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source took more node visits than one presentation makes.
            OverBudget,
        }
    }
}

/// The columns a broken continuation is indented by.
const CONTINUATION: u32 = 2;

/// The maximum scheduled node visits in either presentation pass.
///
/// A well-formed type or value of any size a reader would read fits many
/// times over; the bound is reached by a malformed source — a cycle — whose
/// presentation is then `?` rather than a walk that does not end.
const VISIT_BUDGET: u32 = 0x0001_0000;

/// Fixed or computed text a leaf holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Glyphs<'text>(&'text str);

/// An owned spelling computed for one leaf.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Spelled(String);

/// A name generated for a dependent arrow's binder.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct BinderName(String);

/// The position of a candidate binder name in the order names are tried.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Ordinal(u32);

/// How many binders — of dependent arrows and of static abstractions — are
/// open at a point of the walk; read as a position, the binder that many
/// binders in.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct OpenBinders(usize);

/// How many arguments one spelled application holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Arity(usize);

/// The sort of node a former is, as far as a position cares.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
    /// A value.
    Value,
    /// A computation term.
    Computation,
    /// No former at all: admitted anywhere, spelled `?`.
    Unknown,
}

/// The sort of node `former` is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the value-type formers answer [`Kind::ValueType`], the
///   computation-type formers [`Kind::CompType`], the value formers
///   [`Kind::Value`], a computation [`Kind::Computation`], and an unreadable
///   handle [`Kind::Unknown`].
/// - provides: the check that a node fills the position it stands in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite golden type and value fixtures observe the
///   former partition through exact spelling, while misplaced bridges expose
///   cross-family classifications. Payload values are not classified here.
/// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
#[anodized::spec(ensures: |ret| match ret {
    | Kind::ValueType => matches!(*former, Former::BaseType(_) | Former::UnitType | Former::Product(..)
        | Former::Sum(..) | Former::ThunkType(_) | Former::Universe { .. } | Former::TypeLift
        | Former::Element(_) | Former::Abstract(_) | Former::StaticPi { .. }),
    | Kind::CompType => matches!(*former, Former::Returner(_) | Former::Arrow { .. }
        | Former::Pi { .. } | Former::ComputationElement(_)),
    | Kind::Value => matches!(*former, Former::Variable { .. } | Former::Constant(_) | Former::Unit
        | Former::Literal(_) | Former::Pair(..) | Former::Injection(..) | Former::Thunk | Former::ValueLift
        | Former::Quote(_) | Former::QuoteComputation(_) | Former::StaticLambda(_) | Former::StaticApplication(..)),
    | Kind::Computation => matches!(*former, Former::Computation),
    | Kind::Unknown => matches!(*former, Former::Unreadable),
})]
const fn kind<Node>(former: &Former<'_, Node>) -> Kind
{
    match *former {
        | Former::BaseType(_)
        | Former::UnitType
        | Former::Product(..)
        | Former::Sum(..)
        | Former::ThunkType(_)
        | Former::Universe { .. }
        | Former::TypeLift
        | Former::Element(_)
        | Former::Abstract(_)
        | Former::StaticPi { .. } => Kind::ValueType,
        | Former::Returner(_)
        | Former::Arrow { .. }
        | Former::Pi { .. }
        | Former::ComputationElement(_) => Kind::CompType,
        | Former::Variable { .. }
        | Former::Constant(_)
        | Former::Unit
        | Former::Literal(_)
        | Former::Pair(..)
        | Former::Injection(..)
        | Former::Thunk
        | Former::ValueLift
        | Former::Quote(_)
        | Former::QuoteComputation(_)
        | Former::StaticLambda(_)
        | Former::StaticApplication(..) => Kind::Value,
        | Former::Computation => Kind::Computation,
        | Former::Unreadable => Kind::Unknown,
    }
}

/// The node sorts a position admits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Admits
{
    /// A value type or a computation type.
    Type,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
    /// A value.
    Value,
}

/// How the walk treats a node it reaches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The node fits its position: spell its former.
    Spell,
    /// The node is a value at the depth limit: write `<deep>`.
    Deep,
    /// The node is of a sort its position does not admit: write `?`.
    Misplaced,
}

/// How the walk treats a node of `kind` at `depth` in a position admitting
/// `admits`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Reach::Deep`] for a value position at or past [`DEPTH_LIMIT`];
///   otherwise [`Reach::Spell`] when the position admits the kind — an unknown
///   node is admitted everywhere — and [`Reach::Misplaced`] when it does not.
/// - provides: the one rule both the scan and the walk stop by, so the two
///   reach the same nodes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — misplaced bridges and deep values observe refusal; the
///   exact depth boundary with an unknown former separates depth-first
///   precedence from admission. Arbitrary source behavior is not involved.
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
/// - witness: `walk::tests::depth_boundaries_preserve_precedence_and_saturation`
#[anodized::spec(ensures: |ret| {
    let deep = admits == Admits::Value && depth.0 >= DEPTH_LIMIT.0;
    let admitted = matches!((admits, kind), (_, Kind::Unknown)
        | (Admits::Type, Kind::ValueType | Kind::CompType)
        | (Admits::ValueType, Kind::ValueType) | (Admits::CompType, Kind::CompType)
        | (Admits::Value, Kind::Value));
    (ret == Reach::Deep) == deep && (ret == Reach::Spell) == (!deep && admitted)
        && (ret == Reach::Misplaced) == (!deep && !admitted)
})]
fn reach(
    admits: Admits,
    depth: ValueDepth,
    kind: Kind,
) -> Reach
{
    if admits == Admits::Value && depth >= DEPTH_LIMIT {
        return Reach::Deep;
    }
    match (admits, kind) {
        | (_, Kind::Unknown)
        | (Admits::Type, Kind::ValueType | Kind::CompType)
        | (Admits::ValueType, Kind::ValueType)
        | (Admits::CompType, Kind::CompType)
        | (Admits::Value, Kind::Value) => Reach::Spell,
        | (Admits::Type, Kind::Value | Kind::Computation)
        | (Admits::ValueType, Kind::CompType | Kind::Value | Kind::Computation)
        | (Admits::CompType, Kind::ValueType | Kind::Value | Kind::Computation)
        | (Admits::Value, Kind::ValueType | Kind::CompType | Kind::Computation) => Reach::Misplaced,
    }
}

/// One child a former reads, and what its position admits.
#[derive(Clone, Copy, Debug)]
struct Slot<Node>
{
    /// The child.
    node: Node,
    /// What its position admits.
    admits: Admits,
}

/// The children a former reads, in reading order.
#[derive(Clone, Copy, Debug)]
enum Children<Node>
{
    /// A leaf.
    None,
    /// One child.
    One(Slot<Node>),
    /// Two children, first then second.
    Two(Slot<Node>, Slot<Node>),
}

/// The children `former` reads, each with what its position admits.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a product's and a sum's operands and a static Pi's domain and
///   codomain admit value types; a thunk type's body and a quoted computation
///   type admit computation types; a returner's result, an arrow's and a
///   dependent arrow's domain and a quoted value type admit value types, the
///   arrows' codomains computation types; a decode's code, a pair's items, an
///   injection's body, a static abstraction's body and a static application's
///   operator and argument admit values; every other former is a leaf.
/// - provides: the one table of child positions the scan and the walk share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite composite grammar fixtures and misplaced bridge
///   children observe arity, child order and admitted families. Static
///   abstraction and application fixtures cover their value positions;
///   arbitrary node representations are outside this spelling evidence.
/// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
#[anodized::spec(ensures: |ret| match *former {
    | Former::Product(..) | Former::Sum(..) | Former::StaticPi { .. } => matches!(ret,
        Children::Two(Slot { admits: Admits::ValueType, .. }, Slot { admits: Admits::ValueType, .. })),
    | Former::Arrow { .. } | Former::Pi { .. } => matches!(ret,
        Children::Two(Slot { admits: Admits::ValueType, .. }, Slot { admits: Admits::CompType, .. })),
    | Former::Pair(..) | Former::StaticApplication(..) => matches!(ret,
        Children::Two(Slot { admits: Admits::Value, .. }, Slot { admits: Admits::Value, .. })),
    | Former::ThunkType(_) | Former::QuoteComputation(_) => matches!(ret,
        Children::One(Slot { admits: Admits::CompType, .. })),
    | Former::Returner(_) | Former::Quote(_) => matches!(ret,
        Children::One(Slot { admits: Admits::ValueType, .. })),
    | Former::Element(_) | Former::ComputationElement(_) | Former::Injection(..) | Former::StaticLambda(_) => matches!(ret,
        Children::One(Slot { admits: Admits::Value, .. })),
    | _ => matches!(ret, Children::None),
})]
fn children<Node>(former: &Former<'_, Node>) -> Children<Node>
where
    Node: Copy,
{
    let slot = |node: Node, admits: Admits| Slot { node, admits };
    match *former {
        | Former::Product(first, second)
        | Former::Sum(first, second)
        | Former::StaticPi {
            domain: first,
            codomain: second,
        } => Children::Two(
            slot(first, Admits::ValueType),
            slot(second, Admits::ValueType),
        ),
        | Former::Arrow { domain, codomain } | Former::Pi { domain, codomain } => Children::Two(
            slot(domain, Admits::ValueType),
            slot(codomain, Admits::CompType),
        ),
        | Former::Pair(first, second) | Former::StaticApplication(first, second) => {
            Children::Two(slot(first, Admits::Value), slot(second, Admits::Value))
        },
        | Former::ThunkType(child) | Former::QuoteComputation(child) => {
            Children::One(slot(child, Admits::CompType))
        },
        | Former::Returner(child) | Former::Quote(child) => {
            Children::One(slot(child, Admits::ValueType))
        },
        | Former::Element(child)
        | Former::ComputationElement(child)
        | Former::Injection(_, child)
        | Former::StaticLambda(child) => Children::One(slot(child, Admits::Value)),
        | Former::BaseType(_)
        | Former::UnitType
        | Former::Universe { .. }
        | Former::TypeLift
        | Former::Abstract(_)
        | Former::Variable { .. }
        | Former::Constant(_)
        | Former::Unit
        | Former::Literal(_)
        | Former::Thunk
        | Former::ValueLift
        | Former::Computation
        | Former::Unreadable => Children::None,
    }
}

/// The depth a former's children stand at.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one deeper than `depth` below a value former, saturating at the
///   counter ceiling; `depth` itself below any other former.
/// - provides: the value-depth count [`DEPTH_LIMIT`] bounds.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the exact cutoff and maximum counter distinguish missed
///   increments, increments in type positions and wrapping; the deep value
///   golden observes the resulting presentation boundary.
/// - witness: `walk::tests::depth_boundaries_preserve_precedence_and_saturation`
/// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
#[anodized::spec(ensures: |ret| ret.0 == if kind == Kind::Value { depth.0.saturating_add(1_u32) } else { depth.0 })]
fn below(
    depth: ValueDepth,
    kind: Kind,
) -> ValueDepth
{
    if kind == Kind::Value {
        depth.deeper()
    }
    else {
        depth
    }
}

/// How loosely a spelled piece binds, tightest first.
///
/// A piece stands bare in a slot that admits its binding and is parenthesized
/// in one that admits only tighter pieces. The order is the grammar's: an
/// atom, then the bridges, then `*`, then `+`, then `->`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Binding
{
    /// A name, a literal, a universe, a bracketed form.
    Atom,
    /// `+U C` or `-F A`.
    Prefix,
    /// `A * B`.
    Product,
    /// `A + B`.
    Sum,
    /// `A -> C`, `(x : A) -> C`, or the static abstraction `\a. v`, whose
    /// body runs as far right as an arrow's codomain.
    Arrow,
}

/// One finished document and how it binds.
#[derive(Clone, Copy, Debug)]
struct Piece
{
    /// The document.
    doc: DocId,
    /// How loosely it binds.
    binding: Binding,
}

/// The two bridges between the sorts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Prefix
{
    /// The suspension `+U C`.
    Thunk,
    /// The returner `-F A`.
    Returner,
}

/// The two infix value-type formers, both right-associative.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Infix
{
    /// The product `A * B`.
    Product,
    /// The sum `A + B`.
    Sum,
}

impl Infix
{
    /// The symbol after the left operand, with its leading space.
    ///
    /// # Specification
    /// - ensures: a leading space followed by `*` for a product or `+` for a
    ///   sum.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — product and sum spellings in the finite grammar
    ///   fixtures distinguish swapped operators and missing separators.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    #[anodized::spec(ensures: |ret| matches!((self, ret.0.as_bytes()),
        (Self::Product, &[b' ', b'*']) | (Self::Sum, &[b' ', b'+'])
    ))]
    const fn glyphs(self) -> Glyphs<'static>
    {
        match self {
            | Self::Product => Glyphs(" *"),
            | Self::Sum => Glyphs(" +"),
        }
    }

    /// How the joined piece binds.
    ///
    /// # Specification
    /// - ensures: product binding for a product, sum binding for a sum.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested products and sums in the grammar fixtures
    ///   distinguish reversed precedence and unnecessary parentheses; other
    ///   binding classes are not returned by this function.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    #[anodized::spec(ensures: |ret| matches!((self, ret),
        (Self::Product, Binding::Product) | (Self::Sum, Binding::Sum)
    ))]
    const fn binding(self) -> Binding
    {
        match self {
            | Self::Product => Binding::Product,
            | Self::Sum => Binding::Sum,
        }
    }

    /// The loosest left operand that stands bare.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one step tighter than the former itself, so a left operand of
    ///   the same former is parenthesized.
    /// - provides: the left half of right association.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — left- and right-nested product and sum fixtures
    ///   distinguish a missing left parenthesis and lost right association.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    #[anodized::spec(ensures: |ret| matches!((self, ret),
        (Self::Product, Binding::Prefix) | (Self::Sum, Binding::Product)
    ))]
    const fn left(self) -> Binding
    {
        match self {
            | Self::Product => Binding::Prefix,
            | Self::Sum => Binding::Product,
        }
    }
}

/// The bracketed value formers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Bracket
{
    /// A pair `(a, b)`.
    Pair,
    /// A left injection `Inl(v)`.
    Left,
    /// A right injection `Inr(v)`.
    Right,
}

/// How one join combines the finished pieces below it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Join
{
    /// A bridge over one operand.
    Prefix(Prefix),
    /// An infix former over two operands.
    Infix(Infix),
    /// An arrow over its domain and codomain.
    Arrow,
    /// A dependent arrow over its domain and codomain, its binder named by the
    /// binders open where the join runs.
    Pi,
    /// A static abstraction over its body, its binder named as a dependent
    /// arrow's is.
    StaticLambda,
    /// An operator applied to this many arguments, the spine of static
    /// applications it was written as.
    Apply(Arity),
    /// A bracketed value former over its items.
    Bracket(Bracket),
}

/// One unit of the walk's pending work.
#[derive(Clone, Copy, Debug)]
enum Task<Node>
{
    /// Spell one node in a position admitting `admits`.
    Visit
    {
        /// The node.
        node: Node,
        /// What the position admits.
        admits: Admits,
        /// How many value formers enclose the node.
        depth: ValueDepth,
    },
    /// Open the binder of the dependent arrow or static abstraction whose
    /// body follows.
    Bind,
    /// Close that binder.
    Unbind,
    /// Combine finished pieces.
    Join(Join),
}

/// What a walk produced.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Walked
{
    /// The document of the root, and whether it says the whole of it.
    Built
    {
        /// The root's document.
        doc: DocId,
        /// Whether every node was spelled in full.
        fidelity: Fidelity,
    },
    /// The source took more visits than one presentation makes.
    OverBudget,
}

/// The names dependent arrows' binders take, by position.
///
/// The names are `a`, `b`, …, `z`, then `a1`, `b1`, …, skipping every name a
/// node of the term already spells, so a binder never reads as a constant or
/// an abstract type the term mentions.
#[derive(Debug)]
struct Binders<'names>
{
    /// The names the term's constants and abstract types spell.
    mentioned: BTreeSet<Name<'names>>,
    /// The names generated so far, outermost binder first.
    generated: Vec<BinderName>,
    /// The next candidate to consider.
    next: Ordinal,
}

impl<'names> Binders<'names>
{
    /// Binders that avoid every name in `mentioned`.
    ///
    /// # Specification
    /// trivial.
    const fn new(mentioned: BTreeSet<Name<'names>>) -> Self
    {
        Self {
            mentioned,
            generated: Vec::new(),
            next: Ordinal(0_u32),
        }
    }

    /// The name of the binder at `position`, outermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: cached positions borrow their stored names; distinct
    ///   positions answer distinct names; no answer is a mentioned name.
    /// - provides: the binder of a dependent arrow and the occurrences that
    ///   name it.
    /// - fails: [`binder::Absent::Exhausted`] when the candidate counter cannot
    ///   advance, before issuing its maximum ordinal; cached names still
    ///   resolve.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested arrows and a mentioned first name distinguish
    ///   capture and reordered generation. A counter at its maximum exposes the
    ///   refusal boundary and verifies that cached positions remain available;
    ///   the intervening billions of candidates are not allocated.
    /// - witness: `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `goldens::tests::a_binder_skips_the_names_the_type_mentions`
    /// - witness: `walk::tests::binder_exhaustion_preserves_existing_names`
    #[anodized::spec(
        captures: [cached = self.generated.get(position.0).map(|name| name.0.as_ptr())],
        ensures: |ret| match ret {
            | Maybe::Present(name) => cached.is_none_or(|held| core::ptr::eq(held, name.0.as_ptr()))
                && name.0.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
                && name.0.get(1..).is_some_and(|round| round.is_empty()
                    || round.parse::<u32>().is_ok_and(|value| value > 0_u32)),
            | Maybe::Absent(_) => cached.is_none(),
        },
    )]
    fn name_at(
        &mut self,
        position: OpenBinders,
    ) -> Maybe<&BinderName, binder::Absent>
    {
        while self.generated.len() <= position.0 {
            let Maybe::Present(name) = candidate(self.next)
            else {
                return Maybe::Absent(binder::Absent::Exhausted);
            };
            let Some(next) = self.next.0.checked_add(1_u32)
            else {
                return Maybe::Absent(binder::Absent::Exhausted);
            };
            self.next = Ordinal(next);
            if !self.mentioned.contains(name.0.as_str()) {
                self.generated.push(name);
            }
        }
        self.generated
            .get(position.0)
            .map_or(Maybe::Absent(binder::Absent::Exhausted), Maybe::Present)
    }
}

/// The candidate binder name at `ordinal`: a letter, then the round after the
/// first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `a` through `z` for the first twenty-six ordinals, then the
///   letters again followed by their round; distinct ordinals answer distinct
///   names.
/// - provides: the candidates [`Binders::name_at`] filters.
/// - fails: never on a representable ordinal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — alphabet endpoints, two round transitions and the maximum
///   ordinal distinguish off-by-one letters, missing suffixes and overflow. The
///   remaining ordinal interval is not enumerated.
/// - witness: `walk::tests::candidate_names_cross_rounds_without_losing_the_last_ordinal`
/// - witness: `goldens::tests::a_binder_skips_the_names_the_type_mentions`
#[anodized::spec(ensures: |ref ret| match *ret {
    | Maybe::Present(ref name) => {
        let letter = name.0.as_bytes().first().copied().and_then(|byte| byte.checked_sub(b'a'));
        let round = name.0.get(1..).and_then(|text| if text.is_empty() { Some(0_u32) } else { text.parse::<u32>().ok() });
        letter.is_some_and(|offset| offset < 26_u8)
            && round.and_then(|value| value.checked_mul(26_u32))
                .and_then(|base| base.checked_add(u32::from(letter?))) == Some(ordinal.0)
    },
    | Maybe::Absent(_) => false,
})]
fn candidate(ordinal: Ordinal) -> Maybe<BinderName, binder::Absent>
{
    let letters = 26_u32;
    let (Some(offset), Some(round)) = (
        ordinal.0.checked_rem(letters),
        ordinal.0.checked_div(letters),
    )
    else {
        return Maybe::Absent(binder::Absent::Exhausted);
    };
    let Some(letter) = u8::try_from(offset)
        .ok()
        .and_then(|offset| b'a'.checked_add(offset))
    else {
        return Maybe::Absent(binder::Absent::Exhausted);
    };
    let letter = char::from(letter);
    Maybe::Present(BinderName(if round == 0_u32 {
        String::from(letter)
    }
    else {
        format!("{letter}{round}")
    }))
}

/// Every constant or abstract-type name encountered under `root`, including
/// malformed names that the spelling pass will replace with `?`.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the names encountered from `root` in a position admitting
///   `admits`, at most one distinct name per allowed visit; absent when that
///   scan takes more than the visit budget.
/// - provides: the names binders must avoid, and the bound on the walk.
/// - fails: never; an over-long scan is an absence.
/// - panics: none.
/// - intension: the walk's traversal on an explicit stack, stopped by [`reach`]
///   and descending by [`children`] exactly as the walk does.
///
/// # Adequacy
/// - hypothesis: L3 — a stable cyclic source refuses, and a binder skips an
///   encountered name. The retained scan-to-walk mutation fixture bounds only
///   subsequent traversal, not name consistency for changing sources.
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `goldens::tests::a_binder_skips_the_names_the_type_mentions`
/// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
#[anodized::spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref names) => u32::try_from(names.len()).is_ok_and(|count| count <= VISIT_BUDGET),
    Maybe::Absent(scan::Absent::OverBudget) => true,
})]
fn mentioned<S>(
    source: &S,
    root: S::Node,
    admits: Admits,
) -> Maybe<BTreeSet<Name<'_>>, scan::Absent>
where
    S: Source + ?Sized,
{
    let mut names = BTreeSet::new();
    let mut pending = Vec::from([(root, admits, ValueDepth::ROOT)]);
    let mut visits = 0_u32;
    while let Some((node, admits, depth)) = pending.pop() {
        visits = visits.saturating_add(1_u32);
        if visits > VISIT_BUDGET {
            return Maybe::Absent(scan::Absent::OverBudget);
        }
        let former = source.read(node);
        let kind = kind(&former);
        if reach(admits, depth, kind) != Reach::Spell {
            continue;
        }
        if let Former::Abstract(name) | Former::Constant(name) = former {
            let _fresh = names.insert(name);
        }
        let below = below(depth, kind);
        match children(&former) {
            | Children::None => {},
            | Children::One(only) => pending.push((only.node, only.admits, below)),
            | Children::Two(first, second) => {
                pending.push((second.node, second.admits, below));
                pending.push((first.node, first.admits, below));
            },
        }
    }
    Maybe::Present(names)
}

/// The surface spelling of the universe of `sort` at `level`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Type` for the value universe at level zero, `Type[-]` for the
///   computation universe there, `Type[+, l]` and `Type[-, l]` at a constant
///   level `l` above zero; absent for a parameter sort or a level that mentions
///   a variable.
/// - provides: the universe spellings the grammar writes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both ground sorts at zero and positive levels, a
///   parameter sort and a variable level distinguish polarity, lost levels and
///   unsupported forms. The fixtures do not enumerate large constants.
/// - witness: `goldens::tests::universes_spell_their_sort_and_level`
#[anodized::spec(ensures: |ref ret| match (sort, ret) {
    | (Sort::Parameter(_), &Maybe::Absent(universe::Absent::ParameterSort)) => true,
    | (Sort::Ground(_), &Maybe::Absent(universe::Absent::LevelVariable)) => level.atoms().next().is_some(),
    | (Sort::Ground(ground), &Maybe::Present(ref text)) => {
        let constant = u64::from(level.constant_part());
        level.atoms().next().is_none() && if constant == 0_u64 {
            text.0 == match ground { GroundSort::Value => "Type", GroundSort::Computation => "Type[-]" }
        } else {
            text.0.strip_prefix(match ground { GroundSort::Value => "Type[+, ", GroundSort::Computation => "Type[-, " })
                .and_then(|tail| tail.strip_suffix(']')).and_then(|digits| digits.parse::<u64>().ok()) == Some(constant)
        }
    },
    | _ => false,
})]
fn universe(
    sort: Sort,
    level: &Level,
) -> Maybe<Spelled, universe::Absent>
{
    let Sort::Ground(ground) = sort
    else {
        return Maybe::Absent(universe::Absent::ParameterSort);
    };
    if level.atoms().next().is_some() {
        return Maybe::Absent(universe::Absent::LevelVariable);
    }
    let constant = u64::from(level.constant_part());
    Maybe::Present(Spelled(match (ground, constant) {
        | (GroundSort::Value, 0_u64) => String::from("Type"),
        | (GroundSort::Computation, 0_u64) => String::from("Type[-]"),
        | (GroundSort::Value, _) => format!("Type[+, {constant}]"),
        | (GroundSort::Computation, _) => format!("Type[-, {constant}]"),
    }))
}

/// The surface spelling of a literal.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an integer as its sign and digits; a string between double quotes
///   with a backslash, a double quote, a line feed, a tab, a carriage return
///   and a nul written as the escapes the lowering decodes, every other
///   character as itself; a numeric literal as its sign, its digits, and its
///   fraction after a point when it has one.
/// - provides: the one spelling of every literal, which holds no line break, so
///   a literal never splits across lines.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite escaped-control string, signed integer and
///   numeric fixtures observe delimiters, sign, digits and fractional parts.
///   Arbitrary Unicode strings and all magnitudes are not enumerated.
/// - witness: `goldens::tests::string_controls_stay_in_one_escaped_literal`
/// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
#[anodized::spec(ensures: |ref ret| !ret.0.contains(['\r', '\n', '\t', '\0']) && match *literal {
    | Literal::Integer(ref integer) => {
        let digits = match integer.sign() {
            Sign::Negative => ret.0.strip_prefix('-'),
            Sign::NonNegative => Some(ret.0.as_str()),
        };
        digits == Some(integer.magnitude().as_ref())
    },
    | Literal::Numeric(ref numeric) => {
        let digits = match numeric.sign() {
            Sign::Negative => ret.0.strip_prefix('-'),
            Sign::NonNegative => Some(ret.0.as_str()),
        };
        let fraction: &str = numeric.fraction().as_ref();
        if fraction.is_empty() { digits == Some(numeric.integer_part().as_ref()) }
        else { digits.and_then(|text| text.split_once('.')) == Some((numeric.integer_part().as_ref(), fraction)) }
    },
    | Literal::Text(_) => ret.0.len() >= 2_usize && ret.0.starts_with('"') && ret.0.ends_with('"'),
})]
fn literal(literal: &Literal) -> Spelled
{
    let sign = |sign: Sign| match sign {
        | Sign::Negative => "-",
        | Sign::NonNegative => "",
    };
    Spelled(match *literal {
        | Literal::Integer(ref integer) => {
            format!("{}{}", sign(integer.sign()), integer.magnitude().as_ref())
        },
        | Literal::Text(ref text) => {
            let content: &str = text.as_ref();
            let mut spelled = String::with_capacity(content.len().saturating_add(2_usize));
            spelled.push('"');
            for character in content.chars() {
                match character {
                    | '\\' => spelled.push_str("\\\\"),
                    | '"' => spelled.push_str("\\\""),
                    | '\n' => spelled.push_str("\\n"),
                    | '\t' => spelled.push_str("\\t"),
                    | '\r' => spelled.push_str("\\r"),
                    | '\0' => spelled.push_str("\\0"),
                    | other => spelled.push(other),
                }
            }
            spelled.push('"');
            spelled
        },
        | Literal::Numeric(ref numeric) => {
            let fraction: &str = numeric.fraction().as_ref();
            let whole = format!(
                "{}{}",
                sign(numeric.sign()),
                numeric.integer_part().as_ref()
            );
            if fraction.is_empty() {
                whole
            }
            else {
                format!("{whole}.{fraction}")
            }
        },
    })
}

/// The walk's state: the builder it writes into, the finished pieces, the
/// open binders and what it has had to approximate.
struct Walk<'walk, 'meter, 'names>
{
    /// The builder every leaf and join is written into.
    builder: &'walk mut DocBuilder<'meter>,
    /// Finished pieces, innermost last.
    pieces: Vec<Piece>,
    /// The binder names by position.
    binders: Binders<'names>,
    /// How many dependent arrows' binders are open.
    open: OpenBinders,
    /// Whether every node so far was spelled in full.
    fidelity: Fidelity,
}

impl Walk<'_, '_, '_>
{
    /// A text leaf.
    ///
    /// # Specification
    /// - requires: `glyphs` holds no line feed, carriage return or tab.
    /// - ensures: one text node holding exactly `glyphs`.
    /// - provides: every leaf of the document.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact literal spellings expose corrupted leaf text; a
    ///   zero text-byte budget exposes swallowed build refusals. Other meters
    ///   and allocation failures are outside these fixtures.
    /// - witness: `goldens::tests::string_controls_stay_in_one_escaped_literal`
    /// - witness: `walk::tests::failed_atoms_do_not_push_pieces_or_restore_fidelity`
    #[anodized::spec(
        requires: !glyphs.0.contains(['\r', '\n', '\t']),
        ensures: |ref ret| match *ret {
            | Ok(doc) => glyphs.0.is_empty() || doc != self.builder.empty(),
            | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn leaf(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<DocId, PresentationError>
    {
        Ok(self.builder.text(TextSource::from(glyphs.0))?)
    }

    /// Pushes a finished atom holding `glyphs`.
    ///
    /// # Specification
    /// - requires: as [`Self::leaf`].
    /// - ensures: one atom piece on the finished stack.
    /// - provides: every leaf former's piece.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf spellings and a zero text-byte budget
    ///   distinguish a missing atom, phantom pieces on failure and a wrong
    ///   failure phase.
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `walk::tests::failed_atoms_do_not_push_pieces_or_restore_fidelity`
    #[anodized::spec(
        requires: !glyphs.0.contains(['\r', '\n', '\t']),
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| match *ret {
            | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
            | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
            | Err(_) => false,
        },
    )]
    fn atom(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<(), PresentationError>
    {
        let doc = self.leaf(glyphs)?;
        self.pieces.push(Piece {
            doc,
            binding: Binding::Atom,
        });
        Ok(())
    }

    /// Pushes an atom that stands for more than it says, and marks the
    /// presentation approximate.
    ///
    /// # Specification
    /// - requires: as [`Self::leaf`].
    /// - ensures: one atom piece holding `glyphs`; the fidelity is approximate
    ///   from here on.
    /// - provides: `?`, `<thunk>` and `<deep>`.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deep, opaque and unreadable nodes expose omitted
    ///   approximation; a refused atom exposes a fidelity reset on failure.
    ///   Unrepresented allocator failures are outside this evidence.
    /// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `walk::tests::failed_atoms_do_not_push_pieces_or_restore_fidelity`
    #[anodized::spec(
        requires: !glyphs.0.contains(['\r', '\n', '\t']),
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.fidelity == Fidelity::Approximate && match *ret {
            | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
            | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
            | Err(_) => false,
        },
    )]
    fn approximate(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<(), PresentationError>
    {
        self.fidelity = Fidelity::Approximate;
        self.atom(glyphs)
    }

    /// Pushes a name, or `?` for a name a line cannot hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an atom holding the name; `?`, approximate, for an empty name
    ///   and one holding a line feed, a carriage return or a tab.
    /// - provides: the spelling of constants and abstract types.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary names, a literal question mark, empty names
    ///   and each forbidden control distinguish content from approximation.
    ///   Other Unicode names are outside these finite fixtures.
    /// - witness: `goldens::tests::fidelity_follows_nodes_not_the_characters_of_a_name`
    /// - witness: `walk::tests::unprintable_names_are_approximate_atoms`
    #[anodized::spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity],
        ensures: |ref ret| {
            let text: &str = name.as_ref();
            self.fidelity == if text.is_empty() || text.contains(['\r', '\n', '\t']) { Fidelity::Approximate } else { fidelity }
                && match *ret {
                    | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
                    | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
                    | Err(_) => false,
                }
        },
    )]
    fn name(
        &mut self,
        name: Name<'_>,
    ) -> Result<(), PresentationError>
    {
        let text: &str = name.as_ref();
        if text.is_empty() || text.contains(['\n', '\r', '\t']) {
            return self.approximate(Glyphs("?"));
        }
        self.atom(Glyphs(text))
    }

    /// Pushes the name an intuitionistic variable `index` binders out reads
    /// as, or `?` for one past every open binder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the name of the binder `index` dependent arrows out from the
    ///   occurrence; `?`, approximate, when fewer binders are open.
    /// - provides: the spelling of a bound type variable.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested binders distinguish reversed de Bruijn order
    ///   and capture; a free variable exposes a fabricated in-scope name. The
    ///   fixtures do not open enough binders to exhaust the candidate counter.
    /// - witness: `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `goldens::tests::a_binder_skips_the_names_the_type_mentions`
    /// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
    #[anodized::spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity],
        ensures: |ref ret| ((fidelity != Fidelity::Approximate && index.0 < self.open.0)
            || self.fidelity == Fidelity::Approximate)
            && match *ret {
                | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
                | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
                | Err(_) => false,
            },
    )]
    fn variable(
        &mut self,
        index: OpenBinders,
    ) -> Result<(), PresentationError>
    {
        let Some(position) = self
            .open
            .0
            .checked_sub(index.0)
            .and_then(|outer| outer.checked_sub(1_usize))
        else {
            return self.approximate(Glyphs("?"));
        };
        match self.binders.name_at(OpenBinders(position)) {
            | Maybe::Present(name) => {
                let name = name.clone();
                self.atom(Glyphs(name.0.as_str()))
            },
            | Maybe::Absent(_) => self.approximate(Glyphs("?")),
        }
    }

    /// The finished piece on top of the stack.
    ///
    /// # Specification
    /// - requires: nothing; an empty stack is reported as unbalanced.
    /// - ensures: the top piece, removed.
    /// - provides: every join's operands.
    /// - fails: an empty stack, which the walk's own scheduling excludes.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Unbalanced`] on an empty stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite composite spellings expose reordered operands;
    ///   an incomplete join and an empty stack expose a swallowed underflow.
    /// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
    /// - witness: `walk::tests::missing_operands_are_unbalanced_not_layout_failures`
    #[anodized::spec(
        captures: [entry = self.pieces.len(), top = self.pieces.last().copied()],
        ensures: |ref ret| match *ret {
            | Ok(piece) => top.is_some_and(|held| held.doc == piece.doc && held.binding == piece.binding)
                && self.pieces.len().checked_add(1_usize) == Some(entry),
            | Err(PresentationError::Unbalanced) => entry == 0_usize && self.pieces.is_empty(),
            | Err(_) => false,
        },
    )]
    fn pop(&mut self) -> Result<Piece, PresentationError>
    {
        self.pieces.pop().ok_or(PresentationError::Unbalanced)
    }

    /// `piece`, parenthesized when it binds looser than `loosest`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the piece's document bare when its binding is at most
    ///   `loosest`, else between parentheses.
    /// - provides: the one parenthesization rule of every slot.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed and nested product, sum, bridge and arrow
    ///   fixtures distinguish wrong precedence and missing parentheses. The
    ///   finite grammar cases do not exhaust all possible composite trees.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    #[anodized::spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(doc) => (doc == piece.doc) == (piece.binding <= loosest),
            | Err(PresentationError::Build(_)) => piece.binding > loosest,
            | Err(_) => false,
        },
    )]
    fn bare_up_to(
        &mut self,
        piece: Piece,
        loosest: Binding,
    ) -> Result<DocId, PresentationError>
    {
        if piece.binding <= loosest {
            return Ok(piece.doc);
        }
        let open = self.leaf(Glyphs("("))?;
        let close = self.leaf(Glyphs(")"))?;
        Ok(self.builder.concat_all([open, piece.doc, close])?)
    }

    /// `head` then a space, or a line break indented two columns.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the inline branch is exactly one space; the broken branch
    ///   starts the continuation two columns in and is the left alternative,
    ///   retained when both alternatives are width-tainted.
    /// - provides: the break after an arrow, an infix symbol and a comma.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — narrow and wide continuations and a zero-column pair
    ///   distinguish missing spaces, wrong indentation and reversed
    ///   width-tainted alternatives. Other widths are not enumerated.
    /// - witness: `goldens::tests::arrow_chain_breaks_before_each_continuation`
    /// - witness: `goldens::tests::doubly_tainted_pair_keeps_the_broken_separator`
    #[anodized::spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(doc) => doc != head,
            | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn space_or_break(
        &mut self,
        head: DocId,
    ) -> Result<DocId, PresentationError>
    {
        let space = self.leaf(Glyphs(" "))?;
        let line = self.builder.hard_line();
        let indented = self.builder.nest(NestAmount::from(CONTINUATION), line)?;
        let choice = self.builder.choice(indented, space)?;
        Ok(self.builder.concat(head, choice)?)
    }

    /// `head` then nothing, or a line break.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the inline branch is empty; the broken branch puts the closer
    ///   on its own line and is the left alternative, retained when both
    ///   alternatives are width-tainted.
    /// - provides: the break before a bracket's closer.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — narrow and wide brackets and the zero-column pair
    ///   distinguish a misplaced closer, a spurious flat space and reversed
    ///   width-tainted alternatives; other widths are not enumerated.
    /// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
    /// - witness: `goldens::tests::record_value_breaks_fields_at_the_narrow_page`
    /// - witness: `goldens::tests::doubly_tainted_pair_keeps_the_broken_separator`
    #[anodized::spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(doc) => doc != head,
            | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn none_or_break(
        &mut self,
        head: DocId,
    ) -> Result<DocId, PresentationError>
    {
        let none = self.builder.empty();
        let line = self.builder.hard_line();
        let choice = self.builder.choice(line, none)?;
        Ok(self.builder.concat(head, choice)?)
    }

    /// Spells one node, or schedules its children and their join.
    ///
    /// # Specification
    /// - requires: `tasks` is the walk's stack, and `former` is what `source`
    ///   reads at the node.
    /// - ensures: a value at the depth limit finishes as `<deep>`; a node of a
    ///   sort its position does not admit, an unreadable node and a former
    ///   without a surface spelling finish as `?`; a thunk finishes as
    ///   `<thunk>`; a leaf former finishes as its spelling; a composite former
    ///   pushes its join below its children's visits, a dependent arrow's
    ///   codomain and a static abstraction's body between the opening and the
    ///   closing of its binder; a static application schedules its spine as
    ///   [`Self::spine`] does; a decode and a quote push their child's visit
    ///   alone, so the child's piece is theirs.
    /// - provides: one step of the walk.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete grammar fixtures, nested binders and deep or
    ///   misplaced nodes distinguish missing work, reversed children, binder
    ///   scope leakage and lost approximation. Mutable-source fixtures bound
    ///   traversal but do not prove name consistency across mutations.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
    /// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
    /// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
    #[anodized::spec(
        captures: [entry = self.pieces.len(), pending = tasks.len(), opened = self.open, fidelity = self.fidelity],
        ensures: |ref ret| self.open == opened
            && (fidelity != Fidelity::Approximate || self.fidelity == Fidelity::Approximate)
            && match *ret {
                | Ok(()) => (entry.checked_add(1_usize) == Some(self.pieces.len()) && tasks.len() == pending)
                    || (self.pieces.len() == entry && tasks.len() > pending),
                | Err(PresentationError::Build(_)) => self.pieces.len() == entry && tasks.len() == pending,
                | Err(_) => false,
            },
    )]
    fn visit<S>(
        &mut self,
        source: &S,
        former: Former<'_, S::Node>,
        admits: Admits,
        depth: ValueDepth,
        tasks: &mut Vec<Task<S::Node>>,
    ) -> Result<(), PresentationError>
    where
        S: Source + ?Sized,
    {
        let kind = kind(&former);
        match reach(admits, depth, kind) {
            | Reach::Spell => {},
            | Reach::Deep => return self.approximate(Glyphs("<deep>")),
            | Reach::Misplaced => return self.approximate(Glyphs("?")),
        }
        let join = match former {
            | Former::BaseType(BaseType::Integer) => return self.atom(Glyphs("Integer")),
            | Former::BaseType(BaseType::String) => return self.atom(Glyphs("String")),
            | Former::UnitType => return self.atom(Glyphs("Unit")),
            | Former::Unit => return self.atom(Glyphs("()")),
            | Former::Abstract(name) | Former::Constant(name) => return self.name(name),
            | Former::Literal(value) => {
                let spelled = literal(value);
                return self.atom(Glyphs(spelled.0.as_str()));
            },
            | Former::Universe { sort, level } => {
                return match universe(sort, level) {
                    | Maybe::Present(spelled) => self.atom(Glyphs(spelled.0.as_str())),
                    | Maybe::Absent(_) => self.approximate(Glyphs("?")),
                };
            },
            | Former::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => {
                let index = usize::try_from(u32::from(index)).unwrap_or(usize::MAX);
                return self.variable(OpenBinders(index));
            },
            | Former::Thunk => return self.approximate(Glyphs("<thunk>")),
            | Former::BaseType(BaseType::Numeric)
            | Former::TypeLift
            | Former::ValueLift
            | Former::Variable {
                zone: Zone::Linear, ..
            }
            | Former::Computation
            | Former::Unreadable => return self.approximate(Glyphs("?")),
            | Former::Product(..) => Some(Join::Infix(Infix::Product)),
            | Former::Sum(..) => Some(Join::Infix(Infix::Sum)),
            | Former::ThunkType(_) => Some(Join::Prefix(Prefix::Thunk)),
            | Former::Returner(_) => Some(Join::Prefix(Prefix::Returner)),
            | Former::Arrow { .. } | Former::StaticPi { .. } => Some(Join::Arrow),
            | Former::Pi { .. } => Some(Join::Pi),
            | Former::StaticLambda(_) => Some(Join::StaticLambda),
            | Former::Pair(..) => Some(Join::Bracket(Bracket::Pair)),
            | Former::Injection(Side::Left, _) => Some(Join::Bracket(Bracket::Left)),
            | Former::Injection(Side::Right, _) => Some(Join::Bracket(Bracket::Right)),
            | Former::StaticApplication(operator, argument) => {
                Self::spine(source, operator, argument, depth, tasks);
                return Ok(());
            },
            | Former::Element(_)
            | Former::ComputationElement(_)
            | Former::Quote(_)
            | Former::QuoteComputation(_) => None,
        };
        if let Some(join) = join {
            tasks.push(Task::Join(join));
        }
        let below = below(depth, kind);
        let visit = |slot: Slot<S::Node>| Task::Visit {
            node: slot.node,
            admits: slot.admits,
            depth: below,
        };
        let binds_last = matches!(join, Some(Join::Pi | Join::StaticLambda));
        match children(&former) {
            | Children::None => {},
            | Children::One(only) => {
                if binds_last {
                    tasks.push(Task::Unbind);
                }
                tasks.push(visit(only));
                if binds_last {
                    tasks.push(Task::Bind);
                }
            },
            | Children::Two(first, second) => {
                if binds_last {
                    tasks.push(Task::Unbind);
                }
                tasks.push(visit(second));
                if binds_last {
                    tasks.push(Task::Bind);
                }
                tasks.push(visit(first));
            },
        }
        Ok(())
    }

    /// Schedules a static application and the applications under its
    /// operator as one application, `f(a1, …, an)`.
    ///
    /// # Specification
    /// - requires: the application at `depth` applies `operator` to `argument`,
    ///   and `tasks` is the walk's stack.
    /// - ensures: the operator is read down through every static application it
    ///   is, each argument scheduled at the depth the scan reaches it at, until
    ///   an operator that is no application or one at the depth limit, which is
    ///   scheduled as itself; the join over the operator and the arguments,
    ///   left to right, is pushed below their visits, the operator visited
    ///   first.
    /// - provides: the one spelling the surface writes a spine in, which a join
    ///   over one application at a time could not give.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn deepens the depth it reads at by one, and the loop stops at
    /// [`DEPTH_LIMIT`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one- and three-argument spines observe argument order
    ///   and operator parentheses; the exact depth cutoff observes an unpeeled
    ///   operator scheduled before its argument. Longer stable spines and
    ///   arbitrary changing sources are not enumerated.
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `walk::tests::spine_schedules_operator_first_at_the_depth_limit`
    #[anodized::spec(
        captures: [entry = tasks.len()],
        ensures: |()| tasks.get(entry..).is_some_and(|scheduled| {
            let Some((&Task::Join(Join::Apply(Arity(arity))), visits)) = scheduled.split_first()
            else { return false; };
            arity > 0_usize && u32::try_from(arity).is_ok_and(|count| count <= DEPTH_LIMIT.0.max(1_u32))
                && arity.checked_add(1_usize) == Some(visits.len())
                && visits.iter().all(|task| matches!(*task,
                    Task::Visit { admits: Admits::Value, depth: at, .. }
                        if at.0 >= depth.0.saturating_add(1_u32)
                            && at.0 <= DEPTH_LIMIT.0.max(depth.0.saturating_add(1_u32))))
        }),
    )]
    fn spine<S>(
        source: &S,
        operator: S::Node,
        argument: S::Node,
        depth: ValueDepth,
        tasks: &mut Vec<Task<S::Node>>,
    ) where
        S: Source + ?Sized,
    {
        let mut level = below(depth, Kind::Value);
        let mut arguments = Vec::from([(argument, level)]);
        let mut operator = operator;
        while level < DEPTH_LIMIT {
            let Former::StaticApplication(inner, next) = source.read(operator)
            else {
                break;
            };
            level = level.deeper();
            arguments.push((next, level));
            operator = inner;
        }
        tasks.push(Task::Join(Join::Apply(Arity(arguments.len()))));
        for (node, at) in arguments {
            tasks.push(Task::Visit {
                node,
                admits: Admits::Value,
                depth: at,
            });
        }
        tasks.push(Task::Visit {
            node: operator,
            admits: Admits::Value,
            depth: level,
        });
    }

    /// A leaf naming the binder the join at hand closes over, `?` and
    /// approximate when the names ran out.
    ///
    /// # Specification
    /// - requires: the open count names the binder this join closes over.
    /// - ensures: the generated name is a leaf; an exhausted counter yields `?`
    ///   and marks the presentation approximate without adding a piece.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested dependent arrows and static abstractions
    ///   observe the chosen binder and scope. The binder cache witness covers
    ///   counter exhaustion separately; layout refusal at this exact join is
    ///   outside the finite spelling fixtures.
    /// - witness: `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `walk::tests::binder_exhaustion_preserves_existing_names`
    #[anodized::spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity,
            exhausted = self.open.0 >= self.binders.generated.len() && self.binders.next.0 == u32::MAX],
        ensures: |ref ret| self.pieces.len() == entry
            && (fidelity != Fidelity::Approximate || self.fidelity == Fidelity::Approximate)
            && (!exhausted || self.fidelity == Fidelity::Approximate)
            && match *ret {
                | Ok(doc) => doc != self.builder.empty(),
                | Err(PresentationError::Build(_)) => true,
                | Err(_) => false,
            },
    )]
    fn binder(&mut self) -> Result<DocId, PresentationError>
    {
        match self.binders.name_at(self.open) {
            | Maybe::Present(name) => {
                let name = name.clone();
                self.leaf(Glyphs(name.0.as_str()))
            },
            | Maybe::Absent(_) => {
                self.fidelity = Fidelity::Approximate;
                self.leaf(Glyphs("?"))
            },
        }
    }

    /// Combines the finished pieces a join takes into one.
    ///
    /// # Specification
    /// - requires: available operands are the top finished pieces in operand
    ///   order, last on top; application arity comes from a bounded spine.
    /// - ensures: `+U C` and `-F A` with the operand parenthesized unless it is
    ///   an atom; `A * B` and `A + B`, right-associative, the left operand
    ///   parenthesized when it binds as loosely as the former, the right when
    ///   it binds looser, a break after the symbol; `A -> C` with the domain
    ///   bare up to a sum and the codomain bare, a break after the arrow; `(x :
    ///   A) -> C` naming the binder by the binders open outside it, a break
    ///   after the arrow; `\a. v` naming its binder so, a break after the dot;
    ///   `f(a1, …, an)` with the operator parenthesized unless it is an atom;
    ///   `(a, b)`, `Inl(v)` and `Inr(v)`; every list with a break after each
    ///   comma and before the closer.
    /// - provides: every composite spelling.
    /// - fails: a missing operand, which the walk's scheduling excludes, or the
    ///   builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Unbalanced`] for a missing operand and
    /// [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Termination
    /// An application's loops run once per argument its arity counts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite narrow and wide grammar fixtures distinguish
    ///   wrong operators, parentheses, child order and binder scopes. An
    ///   incomplete join exposes missing-operand refusal; arbitrary trees and
    ///   every builder limit are not enumerated.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
    /// - witness: `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `walk::tests::missing_operands_are_unbalanced_not_layout_failures`
    #[anodized::spec(
        captures: [entry = self.pieces.len(), taken = match join {
            Join::Prefix(_) | Join::StaticLambda | Join::Bracket(Bracket::Left | Bracket::Right) => Some(1_usize),
            Join::Infix(_) | Join::Arrow | Join::Pi | Join::Bracket(Bracket::Pair) => Some(2_usize),
            Join::Apply(Arity(arguments)) => arguments.checked_add(1_usize),
        }],
        ensures: |ref ret| match *ret {
            | Ok(()) => taken.and_then(|count| entry.checked_sub(count)).and_then(|rest| rest.checked_add(1_usize)) == Some(self.pieces.len())
                && self.pieces.last().is_some_and(|piece| piece.binding == match join {
                    Join::Prefix(_) => Binding::Prefix,
                    Join::Infix(Infix::Product) => Binding::Product,
                    Join::Infix(Infix::Sum) => Binding::Sum,
                    Join::Arrow | Join::Pi | Join::StaticLambda => Binding::Arrow,
                    Join::Apply(_) | Join::Bracket(_) => Binding::Atom,
                }),
            | Err(PresentationError::Build(_) | PresentationError::Unbalanced) => self.pieces.len() <= entry,
            | Err(PresentationError::Render(_)) => false,
        },
    )]
    fn join(
        &mut self,
        join: Join,
    ) -> Result<(), PresentationError>
    {
        let (doc, binding) = match join {
            | Join::Prefix(prefix) => {
                let operand = self.pop()?;
                let operand = self.bare_up_to(operand, Binding::Atom)?;
                let head = self.leaf(match prefix {
                    | Prefix::Thunk => Glyphs("+U "),
                    | Prefix::Returner => Glyphs("-F "),
                })?;
                (self.builder.concat(head, operand)?, Binding::Prefix)
            },
            | Join::Infix(infix) => {
                let right = self.pop()?;
                let left = self.pop()?;
                let left = self.bare_up_to(left, infix.left())?;
                let right = self.bare_up_to(right, infix.binding())?;
                let symbol = self.leaf(infix.glyphs())?;
                let head = self.builder.concat(left, symbol)?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, right)?, infix.binding())
            },
            | Join::Arrow => {
                let codomain = self.pop()?;
                let domain = self.pop()?;
                let domain = self.bare_up_to(domain, Binding::Sum)?;
                let arrow = self.leaf(Glyphs(" ->"))?;
                let head = self.builder.concat(domain, arrow)?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, codomain.doc)?, Binding::Arrow)
            },
            | Join::Pi => {
                let codomain = self.pop()?;
                let domain = self.pop()?;
                let binder = self.binder()?;
                let open = self.leaf(Glyphs("("))?;
                let colon = self.leaf(Glyphs(" : "))?;
                let arrow = self.leaf(Glyphs(") ->"))?;
                let head = self
                    .builder
                    .concat_all([open, binder, colon, domain.doc, arrow])?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, codomain.doc)?, Binding::Arrow)
            },
            | Join::StaticLambda => {
                let body = self.pop()?;
                let binder = self.binder()?;
                let lead = self.leaf(Glyphs("\\"))?;
                let dot = self.leaf(Glyphs("."))?;
                let head = self.builder.concat_all([lead, binder, dot])?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, body.doc)?, Binding::Arrow)
            },
            | Join::Apply(Arity(count)) => {
                let mut arguments = Vec::with_capacity(count);
                for _ in 0_usize .. count {
                    arguments.push(self.pop()?);
                }
                let operator = self.pop()?;
                let operator = self.bare_up_to(operator, Binding::Atom)?;
                let opener = self.leaf(Glyphs("("))?;
                let mut items = Vec::from([operator, opener]);
                for (position, argument) in arguments.iter().rev().enumerate() {
                    if position > 0_usize {
                        let comma = self.leaf(Glyphs(","))?;
                        items.push(self.space_or_break(comma)?);
                    }
                    items.push(argument.doc);
                }
                let inner = self.builder.concat_all(items)?;
                let inner = self.none_or_break(inner)?;
                let close = self.leaf(Glyphs(")"))?;
                (self.builder.concat(inner, close)?, Binding::Atom)
            },
            | Join::Bracket(bracket) => {
                let mut items = Vec::new();
                match bracket {
                    | Bracket::Pair => {
                        let second = self.pop()?;
                        let first = self.pop()?;
                        let opener = self.leaf(Glyphs("("))?;
                        let comma = self.leaf(Glyphs(","))?;
                        let comma = self.space_or_break(comma)?;
                        items.extend([opener, first.doc, comma, second.doc]);
                    },
                    | Bracket::Left | Bracket::Right => {
                        let body = self.pop()?;
                        let opener = self.leaf(if bracket == Bracket::Left {
                            Glyphs("Inl(")
                        }
                        else {
                            Glyphs("Inr(")
                        })?;
                        items.extend([opener, body.doc]);
                    },
                }
                let inner = self.builder.concat_all(items)?;
                let inner = self.none_or_break(inner)?;
                let close = self.leaf(Glyphs(")"))?;
                (self.builder.concat(inner, close)?, Binding::Atom)
            },
        };
        self.pieces.push(Piece { doc, binding });
        Ok(())
    }
}

/// The document of the node `root` of `source`, in a position admitting
/// `admits`.
///
/// # Specification
/// - requires: `builder` is the builder the document is rendered from.
/// - ensures: the root's document and whether every node was spelled in full;
///   [`Walked::OverBudget`] when either pass exhausts its scheduled-visit
///   budget. A scan refusal builds nothing; a walk refusal may leave partial
///   documents in the builder when the source changes after the scan.
/// - provides: the document [`crate::present_type`] and
///   [`crate::present_value`] lay out.
/// - fails: the builder's refusal, or bookkeeping the walk's scheduling
///   excludes.
/// - panics: none.
/// - intension: one scan and one walk, each on an explicit stack, never
///   recursion; linear in the nodes reached.
///
/// # Errors
/// Returns [`PresentationError::Build`] when the builder refuses and
/// [`PresentationError::Unbalanced`] when the walk ends with other than one
/// finished piece.
///
/// # Adequacy
/// - hypothesis: L3 — the finite golden fixtures expose wrong constructors,
///   breaks and depth cutoffs. A scanned leaf that becomes a cycle exposes a
///   missing second-pass budget through the read count and approximation. Other
///   mutations of a source during presentation are not enumerated.
/// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
#[anodized::spec(ensures: |ref ret| match *ret {
    | Ok(Walked::Built { doc, .. }) => doc != builder.empty(),
    | Ok(Walked::OverBudget) | Err(PresentationError::Build(_) | PresentationError::Unbalanced) => true,
    | Err(PresentationError::Render(_)) => false,
})]
pub fn walk<S>(
    source: &S,
    root: S::Node,
    admits: Admits,
    builder: &mut DocBuilder<'_>,
) -> Result<Walked, PresentationError>
where
    S: Source + ?Sized,
{
    let Maybe::Present(mentioned) = mentioned(source, root, admits)
    else {
        return Ok(Walked::OverBudget);
    };
    let mut walk = Walk {
        builder,
        pieces: Vec::new(),
        binders: Binders::new(mentioned),
        open: OpenBinders(0_usize),
        fidelity: Fidelity::Faithful,
    };
    let mut tasks = Vec::from([Task::Visit {
        node: root,
        admits,
        depth: ValueDepth::ROOT,
    }]);
    let mut remaining = VISIT_BUDGET;
    while let Some(task) = tasks.pop() {
        match task {
            | Task::Visit {
                node,
                admits,
                depth,
            } => {
                let Some(left) = remaining.checked_sub(1_u32)
                else {
                    return Ok(Walked::OverBudget);
                };
                remaining = left;
                walk.visit(source, source.read(node), admits, depth, &mut tasks)?;
            },
            | Task::Bind => walk.open = OpenBinders(walk.open.0.saturating_add(1_usize)),
            | Task::Unbind => walk.open = OpenBinders(walk.open.0.saturating_sub(1_usize)),
            | Task::Join(join) => walk.join(join)?,
        }
    }
    let root = walk.pop()?;
    if !walk.pieces.is_empty() {
        return Err(PresentationError::Unbalanced);
    }
    Ok(Walked::Built {
        doc: root.doc,
        fidelity: walk.fidelity,
    })
}

#[cfg(test)]
mod tests
{
    use core::cell::Cell;

    use gandr_surface_layout::units::PageWidth;

    use super::Fidelity;
    use super::Former;
    use super::Source;
    use super::VISIT_BUDGET;

    /// The root handle of a deliberately changing source.
    #[derive(Clone, Copy, Debug)]
    struct ChangingNode;

    /// A leaf during the scan and an alternating type cycle during the walk.
    #[repr(transparent)]
    struct ChangingSource
    {
        /// Reads already performed, including the initial naming scan.
        reads: Cell<u32>,
    }

    impl Source for ChangingSource
    {
        type Node = ChangingNode;

        /// Returns a finite changing source without hanging a failing witness.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: the read count advances once, saturating; the first read
        ///   is a unit type, later reads alternate the two type bridges until
        ///   the finite cutoff, after which the handle is unreadable.
        /// - provides: a between-pass change that invalidates the scan's bound.
        /// - fails: never.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the public presentation observes approximation
        ///   and a bounded read count when a scanned leaf becomes a cycle. A
        ///   missing walk budget overruns that count; other source mutations
        ///   are outside this fixture, whose own cutoff keeps the failure
        ///   finite.
        /// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
        #[anodized::spec(
            captures: [entry = self.reads.get()],
            ensures: |ret| self.reads.get() == entry.saturating_add(1_u32)
                && matches!(ret, Former::UnitType | Former::ThunkType(_) | Former::Returner(_) | Former::Unreadable),
        )]
        fn read(
            &self,
            _node: ChangingNode,
        ) -> Former<'_, ChangingNode>
        {
            let entry = self.reads.get();
            self.reads.set(entry.saturating_add(1_u32));
            if entry == 0_u32 {
                Former::UnitType
            }
            else if entry >= VISIT_BUDGET.saturating_add(4_u32) {
                Former::Unreadable
            }
            else if entry & 1_u32 == 1_u32 {
                Former::ThunkType(ChangingNode)
            }
            else {
                Former::Returner(ChangingNode)
            }
        }
    }

    /// A source cannot bypass the traversal budget by changing after its scan.
    #[test]
    fn changing_source_is_still_bounded_by_the_walk_budget()
    {
        let source = ChangingSource {
            reads: Cell::new(0_u32),
        };
        let result = crate::present_type(&source, ChangingNode, PageWidth::from(80_u32));
        assert!(
            source.reads.get() <= VISIT_BUDGET.saturating_add(1_u32),
            "read count escaped the scan plus walk bound: {}",
            source.reads.get()
        );
        let presentation = result.expect("the visit budget refuses before layout construction");
        assert_eq!(presentation.as_ref(), "?");
        assert_eq!(presentation.fidelity(), Fidelity::Approximate);
    }

    /// Depth refusal precedes even an unknown kind and only values deepen.
    #[test]
    fn depth_boundaries_preserve_precedence_and_saturation()
    {
        let before = super::ValueDepth(super::DEPTH_LIMIT.0.saturating_sub(1_u32));
        assert_eq!(
            super::reach(super::Admits::Value, before, super::Kind::Unknown),
            super::Reach::Spell
        );
        assert_eq!(
            super::reach(
                super::Admits::Value,
                super::DEPTH_LIMIT,
                super::Kind::Unknown
            ),
            super::Reach::Deep
        );
        assert_eq!(
            super::reach(super::Admits::Type, super::DEPTH_LIMIT, super::Kind::Value),
            super::Reach::Misplaced
        );
        assert_eq!(
            super::reach(
                super::Admits::Type,
                super::DEPTH_LIMIT,
                super::Kind::Unknown
            ),
            super::Reach::Spell
        );
        let ceiling = super::ValueDepth(u32::MAX);
        assert_eq!(super::below(ceiling, super::Kind::Value), ceiling);
        assert_eq!(super::below(before, super::Kind::CompType), before);
        assert_eq!(super::below(before, super::Kind::Value), super::DEPTH_LIMIT);
    }

    /// Candidate spelling crosses alphabet rounds and represents the last
    /// ordinal.
    #[test]
    fn candidate_names_cross_rounds_without_losing_the_last_ordinal()
    {
        for (ordinal, expected) in [
            (0_u32, "a"),
            (25_u32, "z"),
            (26_u32, "a1"),
            (51_u32, "z1"),
            (52_u32, "a2"),
            (u32::MAX, "v165191049"),
        ] {
            assert!(matches!(super::candidate(super::Ordinal(ordinal)),
                super::Maybe::Present(name) if name.0 == expected));
        }
    }

    /// Avoided names and cached positions survive candidate-counter exhaustion.
    #[test]
    fn binder_exhaustion_preserves_existing_names()
    {
        let mut binders = super::Binders::new(super::BTreeSet::from([super::Name::from("a")]));
        assert!(
            matches!(binders.name_at(super::OpenBinders(0_usize)), super::Maybe::Present(name) if name.0 == "b")
        );
        assert!(
            matches!(binders.name_at(super::OpenBinders(1_usize)), super::Maybe::Present(name) if name.0 == "c")
        );
        binders.next = super::Ordinal(u32::MAX);
        assert!(matches!(
            binders.name_at(super::OpenBinders(2_usize)),
            super::Maybe::Absent(super::binder::Absent::Exhausted)
        ));
        assert!(
            matches!(binders.name_at(super::OpenBinders(0_usize)), super::Maybe::Present(name) if name.0 == "b")
        );
        assert_eq!(binders.generated.len(), 2_usize);
    }

    /// Text-budget refusal must not manufacture a piece or erase approximation.
    #[test]
    fn failed_atoms_do_not_push_pieces_or_restore_fidelity()
    {
        let limits = gandr_surface_layout::limits::BuildLimits {
            max_text_bytes: 0_usize.into(),
            ..gandr_surface_layout::limits::BuildLimits::default()
        };
        let mut meter = gandr_surface_layout::limits::BuildMeter::new(limits);
        let mut builder =
            super::DocBuilder::try_new(&mut meter).expect("singleton nodes need no text bytes");
        let mut walk = super::Walk {
            builder: &mut builder,
            pieces: super::Vec::new(),
            binders: super::Binders::new(super::BTreeSet::new()),
            open: super::OpenBinders(0_usize),
            fidelity: Fidelity::Faithful,
        };
        let refusal = super::PresentationError::Build(
            gandr_surface_layout::error::BuildError::LimitExceeded {
                kind: gandr_surface_layout::error::BuildLimitKind::TextBytes,
                limit: 0_u64.into(),
            },
        );
        assert_eq!(walk.atom(super::Glyphs("x")), Err(refusal));
        assert!(walk.pieces.is_empty());
        assert_eq!(walk.fidelity, Fidelity::Faithful);
        assert!(matches!(
            walk.approximate(super::Glyphs("?")),
            Err(super::PresentationError::Build(
                gandr_surface_layout::error::BuildError::LimitExceeded {
                    kind: gandr_surface_layout::error::BuildLimitKind::TextBytes,
                    ..
                }
            ))
        ));
        assert!(walk.pieces.is_empty());
        assert_eq!(walk.fidelity, Fidelity::Approximate);
    }

    /// An incomplete join reports bookkeeping, not a fabricated layout refusal.
    #[test]
    fn missing_operands_are_unbalanced_not_layout_failures()
    {
        let mut meter = gandr_surface_layout::limits::BuildMeter::new(
            gandr_surface_layout::limits::BuildLimits::default(),
        );
        let mut builder = super::DocBuilder::try_new(&mut meter).expect("default limits build");
        let mut walk = super::Walk {
            builder: &mut builder,
            pieces: super::Vec::new(),
            binders: super::Binders::new(super::BTreeSet::new()),
            open: super::OpenBinders(0_usize),
            fidelity: Fidelity::Faithful,
        };
        walk.atom(super::Glyphs("x")).expect("one operand builds");
        assert_eq!(
            walk.join(super::Join::Arrow),
            Err(super::PresentationError::Unbalanced)
        );
        assert!(walk.pieces.is_empty());
        assert!(matches!(
            walk.pop(),
            Err(super::PresentationError::Unbalanced)
        ));
    }

    /// Empty and forbidden-control names cannot masquerade as faithful atoms.
    #[test]
    fn unprintable_names_are_approximate_atoms()
    {
        let mut arena = gandr_core_term::CoreArena::new();
        let constant = arena.value_constant(gandr_kernel_term::ConstantIndex::from(0_usize));
        for invalid in ["", "\r", "\n", "\t"] {
            let names = [super::Name::from(invalid)];
            let source = crate::core_source::CoreSource::new(&arena, &names);
            let result = crate::present_value(
                &source,
                crate::core_source::CoreNode::Value(constant),
                PageWidth::from(80_u32),
            )
            .expect("malformed names are approximated");
            assert_eq!(result.as_ref(), "?");
            assert_eq!(result.fidelity(), Fidelity::Approximate);
        }
    }

    /// At the cutoff the operator remains unpeeled and executes before its
    /// argument.
    #[test]
    fn spine_schedules_operator_first_at_the_depth_limit()
    {
        let mut arena = gandr_core_term::CoreArena::new();
        let inner = arena.value_unit();
        let argument = arena.value_constant(gandr_kernel_term::ConstantIndex::from(0_usize));
        let operator = arena.value_static_application(inner, argument);
        let source = crate::core_source::CoreSource::new(&arena, &[]);
        let operator = crate::core_source::CoreNode::Value(operator);
        let argument = crate::core_source::CoreNode::Value(argument);
        let mut tasks = super::Vec::new();
        super::Walk::spine(
            &source,
            operator,
            argument,
            super::ValueDepth(super::DEPTH_LIMIT.0.saturating_sub(1_u32)),
            &mut tasks,
        );
        assert!(matches!(tasks.as_slice(), [
            super::Task::Join(super::Join::Apply(super::Arity(1_usize))),
            super::Task::Visit { node: found_argument, admits: super::Admits::Value, depth: argument_depth },
            super::Task::Visit { node: found_operator, admits: super::Admits::Value, depth: operator_depth },
        ] if *found_argument == argument && *found_operator == operator
            && *argument_depth == super::DEPTH_LIMIT && *operator_depth == super::DEPTH_LIMIT));
    }
}
