//! The declarations, migrations and flows that the forward witnesses build.
//! The forward unit tests and the tests that readmit through the bridge read
//! them both.

use gandr_core_term::ComponentCount;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::module::check_module;
use crate::report::ModuleReport;

/// A declaration position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct At(pub usize);

/// The declaration at `position`, its origin the position itself.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn declaration(
    At(position): At,
    declared: ValueTypeId,
    defined: ValueId,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position),
        Maybe::Present(declared),
        Maybe::Present(defined),
        OriginToken::from(position),
    )
}

/// Check `module` in a fresh context.
///
/// # Specification
/// trivial.
#[inline]
pub fn judged(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> ModuleReport
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    check_module(&mut context, module)
}

/// A record migration's codes and translator: `Old = (String, Integer)`,
/// `New = String`, and `to_new` keeping the string field.
pub struct Migration
{
    /// `(String, Integer)`.
    pub old: ValueTypeId,
    /// `String`.
    pub new: ValueTypeId,
    /// `U (Old → F New)`.
    pub translator: ValueTypeId,
    /// `thunk (λp. split p as (s, i) in return s)`.
    pub to_new: ValueId,
}

/// The migration fixture.
///
/// # Specification
/// trivial.
#[inline]
pub fn migration(arena: &mut CoreArena) -> Migration
{
    let string = arena.value_type_base(BaseType::String);
    let integer = arena.value_type_base(BaseType::Integer);
    let old = arena.value_type_product(&[string, integer]);
    let pair = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let kept = arena.computation_return(field);
    let split = arena.computation_split(pair, ComponentCount::from(2_usize), kept);
    let lambda = arena.computation_lambda(split);
    let to_new = arena.value_thunk(lambda);
    let returns = arena.comp_type_returner(string);
    let arrow = arena.comp_type_arrow(old, returns);
    let translator = arena.value_type_thunk(arrow);
    Migration {
        old,
        new: string,
        translator,
        to_new,
    }
}

/// `Flow[.A = Type](⌜from⌝, ⌜to⌝)`.
///
/// # Specification
/// trivial.
#[inline]
pub fn flow(
    arena: &mut CoreArena,
    (from, to): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let from = arena.value_quote(from);
    let to = arena.value_quote(to);
    arena.value_type_flow(universe, from, to)
}

/// `U (domain → F result)`.
///
/// # Specification
/// trivial.
#[inline]
pub fn function(
    arena: &mut CoreArena,
    (domain, result): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let returns = arena.comp_type_returner(result);
    let arrow = arena.comp_type_arrow(domain, returns);
    arena.value_type_thunk(arrow)
}
