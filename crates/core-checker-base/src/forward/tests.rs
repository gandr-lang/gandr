use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::ComponentCount;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::equiv::Vocabulary;
use crate::fixture::forward::At;
use crate::fixture::forward::Migration;
use crate::fixture::forward::declaration;
use crate::fixture::forward::flow;
use crate::fixture::forward::function;
use crate::fixture::forward::judged;
use crate::fixture::forward::migration;
use crate::fixture::integer_literal;
use crate::fixture::text_literal;
use crate::forward::Directed;
use crate::refusal::CheckRefusal;
use crate::report::Judged;
use crate::report::ModuleReport;
use crate::report::Verdict;

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

    // A literal inside a list cell is no image of a source leaf.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let list = arena.value_type_list(integer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let nil = arena.value_list_nil();
    let on_nil = arena.computation_return(nil);
    let zero = arena.value_literal(integer_literal());
    let padded = arena.value_list_cons(zero, bound);
    let cell = arena.value_list_cons(head, padded);
    let on_cons = arena.computation_return(cell);
    let case = arena.computation_list_case(bound, on_nil, on_cons);
    let lambda = arena.computation_lambda(case);
    let pad = arena.value_thunk(lambda);
    let translator = function(&mut arena, (list, list));
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (list, list));
    let report = judged(&mut arena, &[
        declaration(At(0), translator, pad),
        declaration(At(1), migrate, forward),
    ]);
    assert_eq!(
        report.judged().get(1).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::ForwardUnsupported {
            at: forward
        }))
    );

    // A translator reading past the first cell cases on the rigid tail, and
    // its image is stuck there.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let list = arena.value_type_list(integer);
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let nil = arena.value_list_nil();
    let on_nil = arena.computation_return(nil);
    let one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let single = arena.value_list_cons(one, nil);
    let on_last = arena.computation_return(single);
    let first = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
    let rest = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let second = arena.value_list_cons(one, rest);
    let both = arena.value_list_cons(first, second);
    let on_more = arena.computation_return(both);
    let tail = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let inner = arena.computation_list_case(tail, on_last, on_more);
    let case = arena.computation_list_case(outer, on_nil, inner);
    let lambda = arena.computation_lambda(case);
    let deeper = arena.value_thunk(lambda);
    let translator = function(&mut arena, (list, list));
    let to_new = arena.value_constant(ConstantIndex::from(0_usize));
    let forward = arena.value_forward(to_new);
    let migrate = flow(&mut arena, (list, list));
    let report = judged(&mut arena, &[
        declaration(At(0), translator, deeper),
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
    let integers = arena.value_type_list(integer);
    let strings = arena.value_type_list(string);
    let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let cell = arena.value_list_cons(head, leaf);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let unsupported = Err(CheckRefusal::ForwardUnsupported { at });
    assert_eq!(
        super::first_order(&mut context, at, empty, Vocabulary::Data),
        unsupported,
        "an empty sum is not first-order"
    );
    assert_eq!(
        super::first_order(&mut context, at, pair, Vocabulary::Data),
        Ok(())
    );
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

    // A list is first-order; its cell reads the head and the tail apart, and
    // the tail stands only at a list type equivalent to its own.
    assert_eq!(
        super::first_order(&mut context, at, integers, Vocabulary::Data),
        Ok(())
    );
    let read = super::leaves(&mut context, at, cell, integers).expect("a cell's leaves");
    assert!(
        matches!(*read.as_slice(), [
            Maybe::Present(super::Leaf::Tail(_)),
            Maybe::Present(super::Leaf::Integer)
        ]),
        "the tail innermost, the head past it: {read:?}"
    );
    assert_eq!(
        super::natural(&mut context, at, leaf, integers, &read),
        Ok(())
    );
    assert_eq!(
        super::natural(&mut context, at, leaf, strings, &read),
        unsupported,
        "a tail at another list type"
    );
    assert_eq!(
        super::natural(&mut context, at, head, integers, &read),
        unsupported,
        "an element leaf at a list position"
    );
}

/// A data type is first-order in the data vocabulary only, and not when it
/// holds itself; a constructor pattern reads its fields' leaves at the types
/// its tag gives them; and an output at a data type is one of its
/// constructors over exactly its own fields, each a leaf of its own atom.
#[test]
fn data_shapes_are_read_constructor_by_constructor()
{
    let mut arena = CoreArena::new();
    let at = arena.value_unit();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let shapes = Arc::new(DataSignature::new(
        Vec::new(),
        Vec::from([Vec::from([integer]), Vec::from([integer, string])]),
        kind,
    ));
    let own = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let naturals = Arc::new(DataSignature::new(
        Vec::new(),
        Vec::from([Vec::new(), Vec::from([own])]),
        kind,
    ));
    let shape = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let natural = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let near = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let far = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let rectangle = |arena: &mut CoreArena, fields: &[ValueId]| {
        arena.value_constructor(
            ConstantIndex::from(0_usize),
            shape,
            ConstructorTag::from(1_usize),
            fields.to_vec(),
        )
    };
    let labelled = rectangle(&mut arena, &[far, near]);
    let swapped = rectangle(&mut arena, &[near, far]);
    let short = rectangle(&mut arena, &[far]);
    let past = arena.value_constructor(
        ConstantIndex::from(0_usize),
        shape,
        ConstructorTag::from(2_usize),
        Vec::new(),
    );
    let circle = arena.value_constructor(
        ConstantIndex::from(0_usize),
        shape,
        ConstructorTag::from(0_usize),
        Vec::from([far]),
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (position, signature) in [shapes, naturals].into_iter().enumerate() {
        context
            .adopt_data(ConstantIndex::from(position), signature)
            .expect("the signature forms");
    }
    let unsupported = Err(CheckRefusal::ForwardUnsupported { at });
    assert_eq!(
        super::first_order(&mut context, at, shape, Vocabulary::Data),
        Ok(())
    );
    for (code, vocabulary, what) in [
        (
            shape,
            Vocabulary::Containers,
            "a data type outside the vocabulary",
        ),
        (natural, Vocabulary::Data, "a data type holding itself"),
    ] {
        assert_eq!(
            super::first_order(&mut context, at, code, vocabulary),
            unsupported,
            "{what}"
        );
    }

    let read = super::leaves(&mut context, at, labelled, shape).expect("a rectangle's leaves");
    assert_eq!(
        read,
        Vec::from([
            Maybe::Present(super::Leaf::String),
            Maybe::Present(super::Leaf::Integer)
        ]),
        "each field at its declared atom, the later one innermost"
    );
    for output in [labelled, circle] {
        assert_eq!(
            super::natural(&mut context, at, output, shape, &read),
            Ok(()),
            "a constructor over leaves of its fields' atoms"
        );
    }
    for (output, what) in [
        (swapped, "a field moved onto a leaf of the other atom"),
        (short, "a constructor short of its fields"),
        (past, "a tag past the table"),
    ] {
        assert_eq!(
            super::natural(&mut context, at, output, shape, &read),
            unsupported,
            "{what}"
        );
    }
}
