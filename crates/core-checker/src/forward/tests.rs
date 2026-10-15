use alloc::vec::Vec;

use gandr_core_term::ComponentCount;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
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
use crate::fixture::integer_literal;
use crate::fixture::text_literal;
use crate::forward::Directed;
use crate::module::Judged;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;

/// A declaration position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// The declaration at `position`, its origin the position itself.
///
/// # Specification
/// trivial.
fn declaration(
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
fn judged(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> ModuleReport
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    check_module(&mut context, module)
}

/// A record migration's codes and translator: `Old = (String, Integer)`,
/// `New = String`, and `to_new` keeping the string field.
struct Migration
{
    /// `(String, Integer)`.
    old: ValueTypeId,
    /// `String`.
    new: ValueTypeId,
    /// `U (Old → F New)`.
    translator: ValueTypeId,
    /// `thunk (λp. split p as (s, i) in return s)`.
    to_new: ValueId,
}

/// The migration fixture.
///
/// # Specification
/// trivial.
fn migration(arena: &mut CoreArena) -> Migration
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

/// `Flow(Type, ⌜from⌝, ⌜to⌝)`.
///
/// # Specification
/// trivial.
fn flow(
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
fn function(
    arena: &mut CoreArena,
    (domain, result): (ValueTypeId, ValueTypeId),
) -> ValueTypeId
{
    let returns = arena.comp_type_returner(result);
    let arrow = arena.comp_type_arrow(domain, returns);
    arena.value_type_thunk(arrow)
}

#[test]
fn a_migration_is_decided_at_every_covering_input()
{
    let mut arena = CoreArena::new();
    let fixture = migration(&mut arena);
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (fixture.old, fixture.new));
    let flowed = arena.value_constant(ConstantIndex::from(1_usize));
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(code, Level::zero());
    let text = arena.value_literal(text_literal());
    let zero = arena.value_literal(integer_literal());
    let old = arena.value_tuple(&[text, zero]);
    let ride = arena.computation_ride(decoded, flowed, old);
    let moved = arena.value_thunk(ride);
    let returns_new = arena.comp_type_returner(fixture.new);
    let suspended = arena.value_type_thunk(returns_new);
    let report = judged(&mut arena, &[
        declaration(At(0), fixture.translator, fixture.to_new),
        declaration(At(1), migrate, forward),
        declaration(At(2), suspended, moved),
    ]);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "the migration is decided and a record rides it to its new code: {report:?}"
    );
    let Some(directed) = report.directed().get(&forward)
    else {
        panic!("the decision is recorded at the forward node");
    };
    let Directed::Forward(ref decided) = *directed
    else {
        panic!("a forward records a forward decision");
    };
    assert_eq!(
        (decided.images().len(), decided.dialogues().len()),
        (1, 1),
        "a record of two leaves covers as one pattern"
    );
    let unfolded = |dialogue: &Vec<ConversionDecision<()>>| {
        dialogue
            .iter()
            .filter(|decision| matches!(decision, ConversionDecision::Unfold { .. }))
            .count()
    };
    assert_eq!(
        decided.dialogues().iter().map(unfolded).collect::<Vec<_>>(),
        [1],
        "the dialogue unfolds the translator once"
    );
}

#[test]
fn the_symmetry_ride_along_a_migration_is_refused()
{
    let mut arena = CoreArena::new();
    let fixture = migration(&mut arena);
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (fixture.old, fixture.new));
    let flowed = arena.value_constant(ConstantIndex::from(1_usize));
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let old = arena.value_quote(fixture.old);
    let reversed = gandr_core_term::identity::back_flow(&mut arena, universe, old, flowed);
    let backward = flow(&mut arena, (fixture.new, fixture.old));
    let returns = arena.comp_type_returner(backward);
    let declared = arena.value_type_thunk(returns);
    let body = arena.value_thunk(reversed);
    let report = judged(&mut arena, &[
        declaration(At(0), fixture.translator, fixture.to_new),
        declaration(At(1), migrate, forward),
        declaration(At(2), declared, body),
    ]);
    assert_eq!(
        report.judged().get(2).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::NonCovariantMotive {
            at: reversed
        })),
        "`back` along a migration is the symmetry ride, refused by its motive"
    );
}

#[test]
fn what_the_rule_cannot_image_it_refuses_by_name()
{
    // A constant string at a string field is no image of a source leaf.
    let mut arena = CoreArena::new();
    let fixture = migration(&mut arena);
    let text = arena.value_literal(text_literal());
    let constant = arena.computation_return(text);
    let lambda = arena.computation_lambda(constant);
    let stamp = arena.value_thunk(lambda);
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (fixture.old, fixture.new));
    let report = judged(&mut arena, &[
        declaration(At(0), fixture.translator, stamp),
        declaration(At(1), migrate, forward),
    ]);
    assert_eq!(
        report.judged().get(1).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::ForwardUnsupported {
            at: forward
        }))
    );
    assert!(
        report.directed().is_empty(),
        "a refused forward records nothing"
    );

    // A string leaf moved to an integer position is not leaf-natural.
    let mut arena = CoreArena::new();
    let fixture = migration(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let integers = arena.value_type_product(&[integer, integer]);
    let pair = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let first = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let second = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let swapped = arena.value_tuple(&[first, second]);
    let returned = arena.computation_return(swapped);
    let split = arena.computation_split(pair, ComponentCount::from(2_usize), returned);
    let lambda = arena.computation_lambda(split);
    let mistyped = arena.value_thunk(lambda);
    let translator = function(&mut arena, (fixture.old, integers));
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (fixture.old, integers));
    let report = judged(&mut arena, &[
        declaration(At(0), translator, mistyped),
        declaration(At(1), migrate, forward),
    ]);
    assert_eq!(
        report.judged().get(1).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::ForwardUnsupported {
            at: forward
        }))
    );

    // A list code is outside the first-order vocabulary.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let list = arena.value_type_list(integer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let same = arena.value_thunk(lambda);
    let translator = function(&mut arena, (list, list));
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (list, list));
    let report = judged(&mut arena, &[
        declaration(At(0), translator, same),
        declaration(At(1), migrate, forward),
    ]);
    assert_eq!(
        report.judged().get(1).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::ForwardUnsupported {
            at: forward
        }))
    );
}

/// The migration, its forward flow at position one, and `arrow(d, c)` over
/// two copies of it at position two, declared at `declared`.
///
/// # Specification
/// trivial.
fn arrowed(
    arena: &mut CoreArena,
    fixture: &Migration,
    declared: ValueTypeId,
) -> (ModuleReport, ValueId, ValueId)
{
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(arena, (fixture.old, fixture.new));
    let domain = arena.value_constant(ConstantIndex::from(1_usize));
    let codomain = arena.value_constant(ConstantIndex::from(1_usize));
    let lifted = arena.value_function_flow(domain, codomain);
    let report = judged(arena, &[
        declaration(At(0), fixture.translator, fixture.to_new),
        declaration(At(1), migrate, forward),
        declaration(At(2), declared, lifted),
    ]);
    (report, lifted, domain)
}

#[test]
fn a_function_flow_forms_in_variance_order()
{
    // d : Old ⇝ New at the domain and c : Old ⇝ New at the codomain relate
    // U (New → F Old) to U (Old → F New).
    let mut arena = CoreArena::new();
    let fixture = migration(&mut arena);
    let reader = function(&mut arena, (fixture.new, fixture.old));
    let writer = function(&mut arena, (fixture.old, fixture.new));
    let declared = flow(&mut arena, (reader, writer));
    let (report, lifted, _) = arrowed(&mut arena, &fixture, declared);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "the arrow's action runs the domain backward and the codomain forward: {report:?}"
    );
    assert!(
        matches!(report.directed().get(&lifted), Some(Directed::Function(_))),
        "the function flow records its classifier"
    );
}

#[test]
fn a_misdirected_boundary_is_refused_by_name()
{
    // Checked against U (Old → F Old) ⇝ U (New → F New), the domain must run
    // New ⇝ Old; the migration runs Old ⇝ New.
    let mut arena = CoreArena::new();
    let fixture = migration(&mut arena);
    let keeper = function(&mut arena, (fixture.old, fixture.old));
    let shrunk = function(&mut arena, (fixture.new, fixture.new));
    let declared = flow(&mut arena, (keeper, shrunk));
    let (report, _, domain) = arrowed(&mut arena, &fixture, declared);
    assert_eq!(
        report.judged().get(2).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::Boundary { at: domain }))
    );
}

#[test]
fn directed_statements_cross_and_replay()
{
    // toNew; migrate = forward(toNew); a record ridden along it; arrow(migrate,
    // migrate); a stay checked at its endpoints; stay then migrate; a reader
    // ridden along the arrow.
    let mut arena = CoreArena::new();
    let fixture = migration(&mut arena);
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (fixture.old, fixture.new));
    let flowed = arena.value_constant(ConstantIndex::from(1_usize));
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(code, Level::zero());
    let text = arena.value_literal(text_literal());
    let zero = arena.value_literal(integer_literal());
    let old = arena.value_tuple(&[text, zero]);
    let ride = arena.computation_ride(decoded, flowed, old);
    let moved = arena.value_thunk(ride);
    let returns_new = arena.comp_type_returner(fixture.new);
    let suspended_new = arena.value_type_thunk(returns_new);
    let reader = function(&mut arena, (fixture.new, fixture.old));
    let writer = function(&mut arena, (fixture.old, fixture.new));
    let lifted_type = flow(&mut arena, (reader, writer));
    let lifted = arena.value_function_flow(flowed, flowed);
    let quoted_old = arena.value_quote(fixture.old);
    let kept = arena.value_stay(quoted_old);
    let kept_type = flow(&mut arena, (fixture.old, fixture.old));
    let sequenced = arena.value_then(kept, flowed);
    let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let widened = arena.value_tuple(&[field, zero]);
    let returned = arena.computation_return(widened);
    let lambda = arena.computation_lambda(returned);
    let read = arena.value_thunk(lambda);
    let lift = arena.value_constant(ConstantIndex::from(3_usize));
    let rewritten = arena.computation_ride(decoded, lift, read);
    let rewritten = arena.value_thunk(rewritten);
    let returns_writer = arena.comp_type_returner(writer);
    let suspended_writer = arena.value_type_thunk(returns_writer);
    let module = [
        declaration(At(0), fixture.translator, fixture.to_new),
        declaration(At(1), migrate, forward),
        declaration(At(2), suspended_new, moved),
        declaration(At(3), lifted_type, lifted),
        declaration(At(4), kept_type, kept),
        declaration(At(5), migrate, sequenced),
        declaration(At(6), suspended_writer, rewritten),
    ];
    let report = judged(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "every directed statement checks: {report:?}"
    );
    assert_eq!(
        report.directed().len(),
        2,
        "the forward flow and the function flow are recorded"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        outcomes
            .iter()
            .all(|outcome| matches!(outcome, crate::bridge::Outcome::Defined { .. })),
        "the kernel replays every erased certificate: {outcomes:?}"
    );
}

/// The rule reads only canonical shapes: an empty sum is not first-order, a
/// pattern tuple short of its product is no pattern, and an output at a unit or
/// a product is a tuple of exactly its arity.
#[test]
fn the_rule_reads_canonical_shapes_at_their_own_arity()
{
    let mut arena = CoreArena::new();
    let at = arena.value_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit = arena.value_type_unit();
    let empty = arena.value_type_sum(&[]);
    let pair = arena.value_type_product(&[integer, string]);
    let single = arena.value_type_product(&[integer]);
    let leaf = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let one = arena.value_tuple(&[leaf]);
    let two = arena.value_tuple(&[leaf, leaf]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let unsupported = Err(CheckRefusal::ForwardUnsupported { at });
    assert_eq!(
        super::first_order(&mut context, at, empty),
        unsupported,
        "an empty sum is not first-order"
    );
    assert_eq!(super::first_order(&mut context, at, pair), Ok(()));
    assert_eq!(
        super::leaves(&mut context, at, one, pair),
        Err(CheckRefusal::MachineInvariant),
        "a pattern short of its product"
    );
    let read = [Maybe::Present(super::Leaf::Integer)];
    assert_eq!(
        super::natural(&mut context, at, one, unit, &read),
        unsupported,
        "a unit's value is the empty tuple"
    );
    assert_eq!(super::natural(&mut context, at, one, single, &read), Ok(()));
    assert_eq!(
        super::natural(&mut context, at, two, single, &read),
        unsupported,
        "a product's value is a tuple of its own arity"
    );
}
