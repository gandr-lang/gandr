//! Forward flows judged, then readmitted through the bridge.

use alloc::vec::Vec;

use gandr_core_checker_base::fixture::forward::At;
use gandr_core_checker_base::fixture::forward::declaration;
use gandr_core_checker_base::fixture::forward::flow;
use gandr_core_checker_base::fixture::forward::function;
use gandr_core_checker_base::fixture::forward::judged;
use gandr_core_checker_base::fixture::forward::migration;
use gandr_core_checker_base::fixture::integer_literal;
use gandr_core_checker_base::fixture::text_literal;
use gandr_core_checker_base::forward::Directed;
use gandr_core_checker_base::refusal::CheckRefusal;
use gandr_core_checker_base::report::Judged;
use gandr_core_checker_base::report::Verdict;
use gandr_core_term::ComponentCount;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Summand;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;

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
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        outcomes.iter().all(|outcome| matches!(
            outcome,
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel replays every erased certificate: {outcomes:?}"
    );
}

/// A list code covers the empty list and one cell over a rigid tail: the
/// identity keeps the tail, and `uncons` moves it unread into a product. Each
/// flow decides two images, a list rides the second, and the kernel replays
/// every erased certificate.
#[test]
fn a_list_migration_moves_its_tail_unread()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let integers = arena.value_type_list(integer);
    let unit = arena.value_type_unit();
    let cell = arena.value_type_product(&[integer, integers]);
    let view = arena.value_type_sum(&[unit, cell]);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));

    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let keep = arena.value_thunk(lambda);
    let empty = arena.value_unit();
    let none = arena.value_injection(Summand::from(0_usize), empty);
    let pair = arena.value_tuple(&[head, bound]);
    let some = arena.value_injection(Summand::from(1_usize), pair);
    let on_nil = arena.computation_return(none);
    let on_cons = arena.computation_return(some);
    let case = arena.computation_list_case(bound, on_nil, on_cons);
    let lambda = arena.computation_lambda(case);
    let uncons = arena.value_thunk(lambda);

    let keep_type = function(&mut arena, (integers, integers));
    let uncons_type = function(&mut arena, (integers, view));
    let kept_type = flow(&mut arena, (integers, integers));
    let viewed_type = flow(&mut arena, (integers, view));
    let to_keep = arena.value_constant(ConstantIndex::from(0_usize));
    let kept = arena.value_forward(to_keep);
    let to_view = arena.value_constant(ConstantIndex::from(2_usize));
    let viewed = arena.value_forward(to_view);
    let flowed = arena.value_constant(ConstantIndex::from(3_usize));
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(code, Level::zero());
    let zero = arena.value_literal(integer_literal());
    let nil = arena.value_list_nil();
    let one = arena.value_list_cons(zero, nil);
    let ride = arena.computation_ride(decoded, flowed, one);
    let moved = arena.value_thunk(ride);
    let returns_view = arena.comp_type_returner(view);
    let suspended = arena.value_type_thunk(returns_view);
    let module = [
        declaration(At(0), keep_type, keep),
        declaration(At(1), kept_type, kept),
        declaration(At(2), uncons_type, uncons),
        declaration(At(3), viewed_type, viewed),
        declaration(At(4), suspended, moved),
    ];
    let report = judged(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "both list flows are decided and a list rides the view: {report:?}"
    );
    for forward in [kept, viewed] {
        let Some(&Directed::Forward(ref decided)) = report.directed().get(&forward)
        else {
            panic!("a forward records a forward decision");
        };
        assert_eq!(
            (decided.images().len(), decided.dialogues().len()),
            (2, 2),
            "the empty list and one cell over the tail"
        );
    }
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        outcomes.iter().all(|outcome| matches!(
            outcome,
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel replays every erased certificate: {outcomes:?}"
    );
}

/// A list ridden cell by cell along a record flow recurses into its tail: at
/// the cell the image waits on the ride over the tail, so it binds the
/// translator's own image of the tail after the cell's three leaves, the
/// cell's trace converts with that image bound, and the kernel replays it. A
/// fold that pads a literal before each cell recurses the same way, and its
/// cell converts with its image bound too, yet it is refused by name: the
/// literal is no image of a leaf.
#[test]
fn a_list_ridden_along_a_flow_recurses_into_its_tail()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let integer = arena.value_type_base(BaseType::Integer);
    let old = arena.value_type_product(&[string, integer]);
    let new = arena.value_type_product(&[integer, string]);
    let olds = arena.value_type_list(old);
    let news = arena.value_type_list(new);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));

    let swapped = arena.value_tuple(&[bound, outer]);
    let returned = arena.computation_return(swapped);
    let split = arena.computation_split(bound, ComponentCount::from(2_usize), returned);
    let lambda = arena.computation_lambda(split);
    let swap = arena.value_thunk(lambda);
    let to_swap = arena.value_constant(ConstantIndex::from(0_usize));
    let renamed = arena.value_forward(to_swap);
    let flowed = arena.value_constant(ConstantIndex::from(1_usize));
    let decoded = arena.value_type_element(bound, Level::zero());
    let motive = arena.value_type_list(decoded);
    let ride = arena.computation_ride(motive, flowed, bound);
    let lambda = arena.computation_lambda(ride);
    let each = arena.value_thunk(lambda);
    let to_each = arena.value_constant(ConstantIndex::from(2_usize));
    let everyone = arena.value_forward(to_each);

    let swap_type = function(&mut arena, (old, new));
    let renamed_type = flow(&mut arena, (old, new));
    let each_type = function(&mut arena, (olds, news));
    let everyone_type = flow(&mut arena, (olds, news));
    let module = [
        declaration(At(0), swap_type, swap),
        declaration(At(1), renamed_type, renamed),
        declaration(At(2), each_type, each),
        declaration(At(3), everyone_type, everyone),
    ];
    let report = judged(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "the records' flow and the lists' flow are both decided: {report:?}"
    );
    let Some(&Directed::Forward(ref decided)) = report.directed().get(&everyone)
    else {
        panic!("a forward records a forward decision");
    };
    let [nil, cell] = *decided.images()
    else {
        panic!("the empty list and one cell over the tail");
    };
    let binders = |image: ValueId| {
        let Some(&Value::Thunk(mut body)) = arena.value(image)
        else {
            panic!("an image is a thunk");
        };
        let mut count = 0_usize;
        while let Some(&Computation::Lambda(inner)) = arena.computation(body) {
            count += 1;
            body = inner;
        }
        assert!(
            matches!(arena.computation(body), Some(&Computation::Return(_))),
            "an image returns beneath its binders"
        );
        count
    };
    assert_eq!(binders(nil), 0, "the empty list binds no leaf");
    assert_eq!(
        binders(cell),
        4,
        "the cell's string, integer and tail, then the tail's image"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        outcomes.iter().all(|outcome| matches!(
            outcome,
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel replays every erased certificate: {outcomes:?}"
    );

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let integers = arena.value_type_list(integer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let nil = arena.value_list_nil();
    let on_nil = arena.computation_return(nil);
    // In the fold's cell branch the folded tail stands at zero and the head
    // at one.
    let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let cell = arena.value_list_cons(head, bound);
    let zero = arena.value_literal(integer_literal());
    let padded = arena.value_list_cons(zero, cell);
    let on_cons = arena.computation_return(padded);
    let fold = arena.computation_list_fold(integer, integers, bound, on_nil, on_cons);
    let lambda = arena.computation_lambda(fold);
    let pads = arena.value_thunk(lambda);
    let to_pads = arena.value_constant(ConstantIndex::from(0_usize));
    let everyone = arena.value_forward(to_pads);
    let pads_type = function(&mut arena, (integers, integers));
    let everyone_type = flow(&mut arena, (integers, integers));
    let report = judged(&mut arena, &[
        declaration(At(0), pads_type, pads),
        declaration(At(1), everyone_type, everyone),
    ]);
    assert_eq!(
        report.judged().get(1).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::ForwardUnsupported {
            at: everyone
        })),
        "a literal padded before each cell is no image of a leaf"
    );
}
