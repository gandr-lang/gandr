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
use proptest::prelude::*;

use crate::compare::Agreement;
use crate::differential::agreement;
use crate::differential::run_on_tiers;
use crate::differential::settled;
use crate::generate::Generated;
use crate::generate::GeneratedRoot;
use crate::generate::applied_binds;
use crate::generate::computations;

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
    /// normalised.
    #[test]
    fn an_entered_closure_answers_as_the_cut_did(generated in prop_oneof![computations(), applied_binds()])
    {
        let mut arena = CommandArena::new();
        let command = focused(&mut arena, &generated)?;
        let written = settled(&run_on_tiers(&arena, command));
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
            let ran = settled(&run_on_tiers(&arena, entered));
            prop_assert_eq!(Agreement::Same, agreement(&written, &ran), "entered, the program read back {:?} against {:?}", ran, written);
        }
    }
}
