//! The declarations and routes that the elaboration's witnesses build. Its
//! unit tests and the session's tests in the checker's top read them both.

use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::Declaration;
use crate::DeclarationContent;
use crate::OriginToken;
use crate::body;
use crate::fixture::integer_literal;

/// A fixture admission position, distinct from counts.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct At(pub usize);

/// Mint a signed fixture declaration at its origin.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn declaration(
    at: At,
    declared: ValueTypeId,
    body: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(at.0),
        Maybe::Present(declared),
        body,
        OriginToken::from(at.0),
    )
}

/// The type a signed fixture declaration states.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn signed(declaration: &Declaration) -> ValueTypeId
{
    match *declaration.content() {
        DeclarationContent::Value {
            signature: Maybe::Present(declared),
            ..
        } => declared,
        ref other @ (DeclarationContent::Value { .. }
        | DeclarationContent::Data(_)
        | DeclarationContent::Codata(_)
        | DeclarationContent::Abstract(_)
        | DeclarationContent::World(_)) => {
            panic!("a signed value declaration, got {other:?}")
        },
    }
}

/// The route's hole, two independent suspensions, and a stable dependent.
pub struct Route
{
    /// Declarations ordered by admission position.
    pub declarations: Vec<Declaration>,
    /// The legitimate code filling the first declaration.
    pub filling: ValueId,
    /// The rigid integer type.
    pub integer: ValueTypeId,
    /// The hole's decoded type.
    pub decoded: ValueTypeId,
    /// The literal both suspensions eventually emit.
    pub literal: ValueId,
}

/// Build the substitution law's finite model.
///
/// # Specification
/// trivial.
#[inline]
pub fn route(arena: &mut CoreArena) -> Route
{
    let universe = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let filling = arena.value_quote(integer);
    let hole = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.value_type_element(hole, Level::zero());
    let literal = arena.value_literal(integer_literal());
    let result = arena.comp_type_returner(decoded);
    let arrow = arena.comp_type_arrow(decoded, result);
    let identity_type = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let declarations = Vec::from([
        declaration(At(0), universe, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), decoded, Maybe::Present(literal)),
        declaration(At(2), decoded, Maybe::Present(literal)),
        declaration(At(3), identity_type, Maybe::Present(identity)),
    ]);
    Route {
        declarations,
        filling,
        integer,
        decoded,
        literal,
    }
}
