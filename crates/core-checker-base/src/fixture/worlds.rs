//! The worlds, migrations and entry points that the worlds witnesses build.
//! The worlds unit tests and the tests that readmit through the bridge read
//! them both.

use alloc::string::String;
use alloc::vec;

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CoreNode;
use crate::Declaration;
use crate::OriginToken;
use crate::TermNode;
use crate::Verdict;
use crate::worlds::Entry;
use crate::worlds::LocatedDefect;

/// An admission position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct At(pub usize);

impl At
{
    /// The position as a constant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constant(self) -> ConstantIndex
    {
        ConstantIndex::from(self.0)
    }

    /// The origin of the declaration at the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn origin(self) -> OriginToken
    {
        OriginToken::from(self.0)
    }
}

/// The spelling of a text literal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Spelled(pub &'static str);

/// The position of the operator's world declaration.
pub const OPERATOR: At = At(0);

/// The position of the seat's world declaration.
pub const SEAT: At = At(1);

/// The world the declaration at `position` declares.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn world(position: At) -> World
{
    World::Declared(position.constant())
}

/// `world operator ;` and `world seat ;`, at their positions.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn worlds() -> [Declaration; 2]
{
    [OPERATOR, SEAT].map(|position| {
        Declaration::world(position.constant(), EffectRow::EMPTY, position.origin())
    })
}

/// The operator's entry: at its own world, holding one capability to the
/// seat's.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn operating() -> Entry
{
    Entry::new(world(OPERATOR), vec![world(SEAT)])
}

/// The text literal `spelled`.
///
/// # Specification
/// trivial.
#[inline]
pub fn text(
    arena: &mut CoreArena,
    Spelled(spelled): Spelled,
) -> ValueId
{
    arena.value_literal(Literal::Text(StringLiteral::new(String::from(spelled))))
}

/// `migrate[w] { body }`, `w` the world declared at `to`.
///
/// # Specification
/// trivial.
#[inline]
pub fn migrate(
    arena: &mut CoreArena,
    to: At,
    body: ComputationId,
) -> ComputationId
{
    arena.computation_world(WorldForm::Migrate {
        world: world(to),
        body,
    })
}

/// The declaration at `position` of type `U (F result)` whose body is
/// `thunk { body }`.
///
/// # Specification
/// trivial.
#[inline]
pub fn entry_point(
    arena: &mut CoreArena,
    position: At,
    result: ValueTypeId,
    body: ComputationId,
) -> Declaration
{
    let returner = arena.comp_type_returner(result);
    let declared = arena.value_type_thunk(returner);
    let suspended = arena.value_thunk(body);
    Declaration::new(
        position.constant(),
        Maybe::Present(declared),
        Maybe::Present(suspended),
        position.origin(),
    )
}

/// The refusal of a located judgement at `at`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn located(
    at: CoreNode,
    defect: LocatedDefect,
) -> Verdict
{
    Verdict::Refused(CheckRefusal::Located { at, defect })
}

/// The node of the computation `term`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn computation(term: ComputationId) -> CoreNode
{
    CoreNode::Term(TermNode::Computation(term))
}
