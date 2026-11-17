//! Abstract closures against the programs they convert.
//!
//! Conversion rewrites every thunk, recursive thunk and copattern object of a
//! focused program into an abstract closure over the context variables it
//! names, and entering a closure redex binds its environment and its frame
//! together, directly or at the end of a bind chain. Neither changes what a
//! program answers: the suites run each generated program as focused,
//! converted and entered on every tier this host has, and compare the
//! readings.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::NodeAddress;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::check_command;
use gandr_core_sequent::convert_all;
use gandr_core_sequent::enter_all;
use gandr_core_sequent::focus_computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use proptest::prelude::*;

use crate::compare::Agreement;
use crate::differential::agreement;
use crate::differential::fired;
use crate::differential::run_on_tiers;
use crate::differential::settled;
use crate::generate::Generated;
use crate::generate::GeneratedRoot;
use crate::generate::Integer;
use crate::generate::applied_binds;
use crate::generate::computations;
use crate::generate::integer;

/// The command a sweep answered for a command.
///
/// # Specification
/// trivial.
fn command_of(swept: NodeAddress) -> Result<CommandId, TestCaseError>
{
    match swept {
        NodeAddress::Command(command) => Ok(command),
        NodeAddress::Producer(_) | NodeAddress::Consumer(_) => Err(TestCaseError::fail(
            "a sweep answers a command for a command",
        )),
    }
}

/// The focused image of a generated computation.
///
/// # Specification
/// trivial.
fn focused(
    arena: &mut CommandArena,
    generated: &Generated,
) -> Result<CommandId, TestCaseError>
{
    let GeneratedRoot::Computation(root) = generated.root
    else {
        return Err(TestCaseError::fail("the strategy yields computations"));
    };
    let mut provenance = Provenance::new();
    focus_computation(
        &generated.core,
        root,
        arena,
        &mut provenance,
        &gandr_core_sequent::Writers::NONE,
    )
    .map_err(|refusal| TestCaseError::fail(alloc::format!("focusing refused: {refusal:?}")))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Every generated program, its closures converted, checks with the free
    /// variables it had and runs to the reading it runs to as written, node for
    /// node.
    #[test]
    fn converted_programs_answer_as_written(generated in computations())
    {
        let mut arena = CommandArena::new();
        let command = focused(&mut arena, &generated)?;
        let written = run_on_tiers(&arena, command);
        let converted = command_of(
            convert_all(&mut arena, NodeAddress::Command(command))
                .map_err(|refusal| TestCaseError::fail(alloc::format!("conversion refused: {refusal:?}")))?,
        )?;
        prop_assert_eq!(check_command(&arena, command), check_command(&arena, converted), "conversion changed what the program binds");
        let ran = run_on_tiers(&arena, converted);
        prop_assert_eq!(Agreement::Same, agreement(&written, &ran), "converted, the program read back {:?} against {:?}", ran, written);
    }

    /// Every generated program, and every generated application of a bind
    /// whose body is a function, converted or not, with every closure redex
    /// entered, runs to what it runs to as written, once both readings are
    /// normalised and every application of a bind is fired at a distance, as
    /// the closure's β fires it.
    #[test]
    fn an_entered_closure_answers_as_the_cut_did(generated in prop_oneof![computations(), applied_binds()])
    {
        let mut arena = CommandArena::new();
        let command = focused(&mut arena, &generated)?;
        let written = fired(&run_on_tiers(&arena, command));
        let converted = command_of(
            convert_all(&mut arena, NodeAddress::Command(command))
                .map_err(|refusal| TestCaseError::fail(alloc::format!("conversion refused: {refusal:?}")))?,
        )?;
        for start in [command, converted] {
            let entered = command_of(
                enter_all(&mut arena, NodeAddress::Command(start))
                    .map_err(|refusal| TestCaseError::fail(alloc::format!("entering refused: {refusal:?}")))?,
            )?;
            prop_assert!(check_command(&arena, entered).is_ok(), "an entered program is ill formed");
            let ran = fired(&run_on_tiers(&arena, entered));
            prop_assert_eq!(Agreement::Same, agreement(&written, &ran), "entered, the program read back {:?} against {:?}", ran, written);
        }
    }
}

/// A function applied through a bind whose head is a case on the variable
/// around it enters at a distance, `λy. (x ← case y of …; λa. return a) 7`
/// as `λy. x ← case y of …; return 7`. The written run keeps the
/// application outside the stuck bind, so the two readings differ once
/// normalised, and agree once each application of a bind fires at a
/// distance.
#[test]
fn an_application_of_a_stuck_bind_fires_at_a_distance_4264()
{
    let mut core = CoreArena::new();
    let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let one = integer(&mut core, Integer(1_i32));
    let two = integer(&mut core, Integer(2_i32));
    let left = core.computation_return(one);
    let right = core.computation_return(two);
    let cased = core.computation_case(scrutinee, &[left, right]);
    let argument = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(argument);
    let function = core.computation_lambda(returned);
    let bound = core.computation_bind(cased, function);
    let seven = integer(&mut core, Integer(7_i32));
    let applied = core.computation_application(bound, seven);
    let root = core.computation_lambda(applied);
    let generated = Generated {
        core,
        root: GeneratedRoot::Computation(root),
    };
    let mut arena = CommandArena::new();
    let command = focused(&mut arena, &generated).expect("the program focuses");
    let entered =
        command_of(enter_all(&mut arena, NodeAddress::Command(command)).expect("the redex enters"))
            .expect("entering answers a command");
    let written = run_on_tiers(&arena, command);
    let ran = run_on_tiers(&arena, entered);
    assert_eq!(
        agreement(&settled(&written), &settled(&ran)),
        Agreement::Differ,
        "normalised, the written reading keeps the application outside the stuck bind"
    );
    assert_eq!(
        agreement(&fired(&written), &fired(&ran)),
        Agreement::Same,
        "fired at a distance, the written reading is the entered one"
    );
}
