//! Focusing and unfocusing over generated and hand-built core terms.
//!
//! The generated suites run over closed, well-typed computations and values
//! from [`crate::generate`]: focusing is total on them, its image passes the
//! typed-IL check closed, every command of it carries the support an
//! independent walk computes, every covariable it mints is the innermost one,
//! and unfocusing reads each image back as the term it came from. The
//! hand-built suite preserves each former's syntax, scope, and provenance
//! through a round trip.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConsumerArity;
use gandr_core_sequent::ConsumerId;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::CovariableIndex;
use gandr_core_sequent::FocusOrigin;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::Introduces;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Route;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_top_value;
use gandr_core_sequent::focus_value;
use gandr_core_sequent::unfocus_command;
use gandr_core_sequent::unfocus_value;
use gandr_core_term::ArenaWatermark;
use gandr_core_term::Binders;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::equal_type_syntax;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::shift_comp_type_under;
use gandr_core_term::shift_computation_under;
use gandr_core_term::shift_value_type_under;
use gandr_core_term::world::WorldForm;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::Summand;
use proptest::prelude::*;

use crate::compare::Agreement;
use crate::compare::same_computation;
use crate::compare::same_value;
use crate::generate::GeneratedRoot;
use crate::generate::Integer;
use crate::generate::computations;
use crate::generate::integer;
use crate::generate::values;

#[test]
fn hand_built_control_cases_cover_every_former()
{
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::memory::MemoryForm;
    use gandr_core_term::world::World;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let one = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let ty = core.value_type_unit();
    let signature = EffectSig::new("Quoted\"interface".into(), [EffectOp {
        name: "op".into(),
        payload: ty,
        reply: ty,
    }])
    .expect("one operation");
    let returned = core.computation_return(unit);
    let identity = core.computation_return(zero);
    let payload = core.computation_return(one);
    let stack = core.value_reify(alloc::sync::Arc::from([
        StackFrame::Apply(unit),
        StackFrame::Bind(identity),
        StackFrame::Project(Component::from(1_usize)),
    ]));
    let stack_return = core.computation_return(stack);
    let performed = core.computation_perform(signature.clone(), "op".into(), unit);
    let resumed = core.computation_resume(zero, payload);
    let handled = core.computation_handle(
        signature.clone(),
        performed,
        identity,
        alloc::sync::Arc::from([EffectClause {
            operation: "op".into(),
            body: resumed,
        }]),
    );
    let exercised = core.computation_exercise(zero, signature.clone(), "op".into(), unit);
    let exercised = core.computation_bind(exercised, identity);
    let scoped = core.computation_scope(
        signature,
        exercised,
        identity,
        alloc::sync::Arc::from([EffectClause {
            operation: "op".into(),
            body: resumed,
        }]),
    );
    let resume_literal = core.computation_resume(stack, returned);
    let resume_captured = core.computation_resume(zero, returned);
    let shifted = core.computation_shift(resume_captured);
    let reset = core.computation_reset(shifted);
    let pair = core.computation_with(&[returned, identity]);
    let under = core.computation_lambda(pair);
    let pair = core.computation_with(&[returned, returned, returned]);
    let projected = core.computation_project(Component::from(2_usize), pair);
    let view = 0_u32.into();
    let resumed_view = core.computation_memory(MemoryForm::Resume { view, value: unit });
    let ended = core.computation_bind(resumed_view, returned);
    let accessed = core.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind: returned },
        held: view,
        place: gandr_core_term::memory::Place::Whole,
        body: ended,
    });
    let aborted_view = core.computation_memory(MemoryForm::Abort { view });
    let aborting = core.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind: identity },
        held: view,
        place: gandr_core_term::memory::Place::Whole,
        body: aborted_view,
    });
    let both = core.computation_bind(accessed, aborting);
    let held = core.computation_memory(MemoryForm::Hold {
        value: unit,
        body: both,
        grade: gandr_core_term::memory::HoldGrade::Many,
    });
    // hold () ; leta y = it ; migrate [host] { return y }
    let held_here = core.computation_world(WorldForm::Hold { value: unit });
    let migrated = core.computation_world(WorldForm::Migrate {
        world: World::Host,
        body: identity,
    });
    let opened = core.computation_world(WorldForm::Leta {
        value: zero,
        body: migrated,
    });
    let worlds = core.computation_bind(held_here, opened);
    for program in [
        stack_return,
        performed,
        handled,
        scoped,
        resume_literal,
        reset,
        under,
        projected,
        held,
        worlds,
    ] {
        let expected = core.value_thunk(program);
        let mut arena = CommandArena::new();
        let command = focus_computation(&core, program, &mut arena, &mut Provenance::new())
            .expect("control focuses");
        assert_eq!(Ok(FreeSet::default()), check_command(&arena, command));
        assert_eq!(Agreement::Same, supports_are_walked(&arena));
        let restored = unfocus_command(&arena, command, &mut core).expect("image unfocuses");
        let actual = core.value_thunk(restored);
        assert_eq!(
            gandr_core_term::CertificateEquality::Equal,
            gandr_core_term::equal_certificate_syntax(&core, expected, actual)
        );
    }
}

/// Every covariable node of an arena is the innermost one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: Same exactly when no recorded consumer is a covariable other than
///   the innermost one, including consumers unreachable from any command.
/// - provides: the covariable part of the focused-image observation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and terminal-only arenas, the innermost covariable
///   and an unreachable outer covariable distinguish vacuous rejection,
///   wrong-family scanning and an ignored unused node. Generated focusing
///   additionally observes the invariant over bounded closed terms; no claim is
///   made about arbitrary transformation passes.
/// - witness: `tests::focus_properties::covariable_observation_includes_unreachable_nodes`
/// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
#[spec(ensures: |ret| (ret == Agreement::Same) ==
    (0_usize .. usize::from(arena.consumer_count())).all(|offset|
        u32::try_from(offset).is_ok_and(|at| arena.consumer(ConsumerId::from(at))
            .is_none_or(|node| !matches!(*node, ConsumerNode::Covariable(index) if index != CovariableIndex::from(0_u32))))))]
fn every_covariable_is_innermost(arena: &CommandArena) -> Agreement
{
    let count = usize::from(arena.consumer_count());
    for offset in 0 .. count {
        let id = ConsumerId::from(u32::try_from(offset).expect("a small arena"));
        if let Some(&ConsumerNode::Covariable(index)) = arena.consumer(id)
            && index != CovariableIndex::from(0_u32)
        {
            return Agreement::Differ;
        }
    }
    Agreement::Same
}

/// The binders a node stands under, per space, counted from the command an
/// oracle walk starts at.
#[derive(Clone, Copy, Debug, Default)]
struct Depth
{
    /// Intuitionistic producer binders.
    producers: u32,
    /// Covariable binders.
    covariables: u32,
    /// Linear producer binders.
    linears: u32,
}

impl Depth
{
    /// The depth under further intuitionistic producer binders and
    /// covariable binders.
    ///
    /// # Specification
    /// trivial.
    fn under(
        self,
        producers: ProducerArity,
        covariables: ConsumerArity,
    ) -> Self
    {
        Self {
            producers: self
                .producers
                .checked_add(u32::try_from(usize::from(producers)).expect("a small arity"))
                .expect("a shallow term"),
            covariables: self
                .covariables
                .checked_add(u32::try_from(usize::from(covariables)).expect("a small arity"))
                .expect("a shallow term"),
            linears: self.linears,
        }
    }
}

/// One node an oracle walk visits, under the binders above it.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// A command.
    Command(CommandId, Depth),
    /// A producer.
    Producer(ProducerId, Depth),
    /// A consumer.
    Consumer(ConsumerId, Depth),
}

/// A free set, as the check answers one.
type Free = (BTreeSet<(Zone, DeBruijnIndex)>, BTreeSet<CovariableIndex>);

/// The free variables and covariables of `command`, by a walk independent of
/// the carried scopes: every occurrence below it, and every index an
/// annotation below it names, counted past the binders above it.
///
/// # Specification
/// - requires: `command` and everything below it resolve.
/// - ensures: each producer variable and covariable an occurrence names past
///   its binders, lowered by them; a linear variable is bound only by a memory
///   form's hold or access body. An annotation's indices are read off its core
///   root, whose support
///   `core_supports_equal_the_shift_machine_on_every_generated_term` holds to
///   the shift machine.
/// - panics: on a node the arena does not hold.
/// - executable: none — this is the reference the carried supports are held to;
///   it is the walk the check ran before scope was carried.
///
/// # Adequacy
/// - hypothesis: L2 — agreement with the check on every command of every
///   generated and hand-built focused term.
/// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
fn walked(
    arena: &CommandArena,
    command: CommandId,
) -> Free
{
    let annotations = arena.annotations();
    let mut free = Free::default();
    let mut stack = alloc::vec![Visit::Command(command, Depth::default())];
    let named = |free: &mut Free, ty, depth: Depth| {
        let support = annotations
            .value_type_support(ty)
            .expect("the annotation resolves");
        for index in support.indices(Zone::Intuitionistic) {
            if let Some(past) = u32::from(index).checked_sub(depth.producers) {
                free.0
                    .insert((Zone::Intuitionistic, DeBruijnIndex::from(past)));
            }
        }
    };
    while let Some(visit) = stack.pop() {
        match visit {
            Visit::Command(id, depth) => match *arena.command(id).expect("the command resolves") {
                CommandNode::Cut {
                    producer, consumer, ..
                }
                | CommandNode::Abandon {
                    stack: producer,
                    continuation: consumer,
                } => {
                    stack.push(Visit::Producer(producer, depth));
                    stack.push(Visit::Consumer(consumer, depth));
                },
                CommandNode::Perform {
                    ref signature,
                    route,
                    payload,
                    continuation,
                    ..
                } => {
                    for ty in signature.types() {
                        named(&mut free, ty, depth);
                    }
                    if let Route::Capability(capability) = route {
                        stack.push(Visit::Producer(capability, depth));
                    }
                    stack.push(Visit::Producer(payload, depth));
                    stack.push(Visit::Consumer(continuation, depth));
                },
                CommandNode::Handle {
                    ref signature,
                    introduces,
                    subject,
                    on_return,
                    ref clauses,
                    continuation,
                } => {
                    for ty in signature.types() {
                        named(&mut free, ty, depth);
                    }
                    let introduced = match introduces {
                        Introduces::Nothing => ProducerArity::ZERO,
                        Introduces::Capability => ProducerArity::ONE,
                    };
                    stack.push(Visit::Command(
                        subject,
                        depth.under(introduced, ConsumerArity::ONE),
                    ));
                    stack.push(Visit::Command(
                        on_return,
                        depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                    ));
                    for clause in clauses.iter() {
                        stack.push(Visit::Command(
                            clause.body,
                            depth.under(ProducerArity::TWO, ConsumerArity::ONE),
                        ));
                    }
                    stack.push(Visit::Consumer(continuation, depth));
                },
                CommandNode::Resume {
                    stack: captured,
                    body,
                    continuation,
                } => {
                    stack.push(Visit::Producer(captured, depth));
                    stack.push(Visit::Command(
                        body,
                        depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                    ));
                    stack.push(Visit::Consumer(continuation, depth));
                },
                CommandNode::Reset { body, continuation } => {
                    stack.push(Visit::Command(
                        body,
                        depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                    ));
                    stack.push(Visit::Consumer(continuation, depth));
                },
                CommandNode::Shift { body, continuation } => {
                    stack.push(Visit::Command(
                        body,
                        depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                    ));
                    stack.push(Visit::Consumer(continuation, depth));
                },
                CommandNode::Memory {
                    ref form,
                    continuation,
                } => {
                    for value in form.values() {
                        stack.push(Visit::Producer(value, depth));
                    }
                    for (body, linears) in form.scoped() {
                        let mut under = depth.under(ProducerArity::ZERO, ConsumerArity::ONE);
                        under.linears = under
                            .linears
                            .checked_add(u32::from(linears))
                            .expect("a shallow term");
                        stack.push(Visit::Command(body, under));
                    }
                    match *form {
                        MemoryForm::Access { held: index, .. }
                        | MemoryForm::Consume { held: index }
                        | MemoryForm::Resume { view: index, .. }
                        | MemoryForm::Abort { view: index } => {
                            if let Some(past) = u32::from(index).checked_sub(depth.linears) {
                                free.0.insert((Zone::Linear, DeBruijnIndex::from(past)));
                            }
                        },
                        MemoryForm::Hold { .. } => {},
                    }
                    stack.push(Visit::Consumer(continuation, depth));
                },
                CommandNode::World {
                    ref form,
                    continuation,
                } => {
                    match *form {
                        WorldForm::Hold { value } => stack.push(Visit::Producer(value, depth)),
                        WorldForm::Leta { value, body } => {
                            stack.push(Visit::Producer(value, depth));
                            stack.push(Visit::Command(
                                body,
                                depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                            ));
                        },
                        WorldForm::Migrate { body, .. } => stack.push(Visit::Command(
                            body,
                            depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                        )),
                    }
                    stack.push(Visit::Consumer(continuation, depth));
                },
            },
            Visit::Producer(id, depth) => {
                match *arena.producer(id).expect("the producer resolves") {
                    ProducerNode::Reify(ref frames) => {
                        for frame in frames.iter() {
                            match *frame {
                                StackFrame::Apply(value) => {
                                    stack.push(Visit::Producer(value, depth));
                                },
                                StackFrame::Bind(body) => {
                                    stack.push(Visit::Command(
                                        body,
                                        depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                                    ));
                                },
                                StackFrame::Project(_) => {},
                            }
                        }
                    },
                    ProducerNode::Primitive { ref arguments, .. } => {
                        for &argument in arguments.iter() {
                            stack.push(Visit::Producer(argument, depth));
                        }
                    },
                    ProducerNode::Variable { zone, index } => {
                        let bound = match zone {
                            Zone::Intuitionistic => depth.producers,
                            Zone::Linear => depth.linears,
                        };
                        if let Some(past) = u32::from(index).checked_sub(bound) {
                            free.0.insert((zone, DeBruijnIndex::from(past)));
                        }
                    },
                    ProducerNode::Constant(_)
                    | ProducerNode::Literal(_)
                    | ProducerNode::Code(_) => {},
                    ProducerNode::Constructor {
                        ref producers,
                        ref consumers,
                        ..
                    } => {
                        for &producer in producers {
                            stack.push(Visit::Producer(producer, depth));
                        }
                        for &consumer in consumers {
                            stack.push(Visit::Consumer(consumer, depth));
                        }
                    },
                    ProducerNode::Thunk { body } | ProducerNode::Mu { body } => {
                        stack.push(Visit::Command(
                            body,
                            depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                        ));
                    },
                    ProducerNode::Fixpoint { body, .. } => {
                        stack.push(Visit::Command(
                            body,
                            depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                        ));
                    },
                    ProducerNode::Cocase { ref arms } => {
                        for arm in arms {
                            let under = depth.under(
                                arm.destructor.producer_arity(),
                                arm.destructor.consumer_arity(),
                            );
                            stack.push(Visit::Command(arm.body, under));
                        }
                    },
                    ProducerNode::Closure {
                        ref environment,
                        code,
                    } => {
                        for &value in environment {
                            stack.push(Visit::Producer(value, depth));
                        }
                        stack.push(Visit::Producer(
                            code,
                            depth
                                .under(ProducerArity::from(environment.len()), ConsumerArity::ZERO),
                        ));
                    },
                    ProducerNode::Decompose(dialogue) => {
                        stack.push(Visit::Producer(dialogue, depth));
                    },
                }
            },
            Visit::Consumer(id, depth) => {
                match *arena.consumer(id).expect("the consumer resolves") {
                    ConsumerNode::Covariable(index) => {
                        if let Some(past) = u32::from(index).checked_sub(depth.covariables) {
                            free.1.insert(CovariableIndex::from(past));
                        }
                    },
                    ConsumerNode::Top => {},
                    ConsumerNode::ListFold {
                        element,
                        result,
                        on_nil,
                        on_cons,
                        continuation,
                    } => {
                        named(&mut free, element, depth);
                        named(&mut free, result, depth);
                        stack.push(Visit::Command(
                            on_nil,
                            depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                        ));
                        stack.push(Visit::Command(
                            on_cons,
                            depth.under(ProducerArity::TWO, ConsumerArity::ONE),
                        ));
                        stack.push(Visit::Consumer(continuation, depth));
                    },
                    ConsumerNode::MuTilde { body } => {
                        stack.push(Visit::Command(
                            body,
                            depth.under(ProducerArity::ONE, ConsumerArity::ZERO),
                        ));
                    },
                    ConsumerNode::Destructor {
                        ref producers,
                        ref consumers,
                        ..
                    } => {
                        for &producer in producers {
                            stack.push(Visit::Producer(producer, depth));
                        }
                        for &consumer in consumers {
                            stack.push(Visit::Consumer(consumer, depth));
                        }
                    },
                    ConsumerNode::Case { ref arms } => {
                        for arm in arms {
                            let under = depth.under(
                                arm.constructor.producer_arity(),
                                arm.constructor.consumer_arity(),
                            );
                            stack.push(Visit::Command(arm.body, under));
                        }
                    },
                    ConsumerNode::DataCase {
                        ref branches, then, ..
                    } => {
                        for &branch in branches {
                            stack.push(Visit::Producer(branch, depth));
                        }
                        stack.push(Visit::Consumer(then, depth));
                    },
                    ConsumerNode::Select { then, .. } => {
                        stack.push(Visit::Consumer(then, depth));
                    },
                }
            },
        }
    }
    free
}

/// Every command of `arena` checks, and its checked free set is the one an
/// independent walk computes.
///
/// # Specification
/// - requires: every command of the arena resolves everything below it.
/// - ensures: Same exactly when, at every command, the check succeeds and
///   answers [`walked`]'s free set.
/// - panics: on a node the arena does not hold.
/// - executable: none — the observation of the witnesses below.
///
/// # Adequacy
/// - hypothesis: L2 — generated and hand-built focused terms over every former
///   the focuser emits.
/// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
/// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
/// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
fn supports_are_walked(arena: &CommandArena) -> Agreement
{
    for offset in 0 .. usize::from(arena.command_count()) {
        let id = CommandId::from(u32::try_from(offset).expect("a small arena"));
        let carried = check_command(arena, id)
            .map(|free| (free.producers().clone(), free.covariables().clone()));
        if carried != Ok(walked(arena, id)) {
            return Agreement::Differ;
        }
    }
    Agreement::Same
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    /// Focusing a closed, well-typed computation succeeds, its image is well
    /// formed and closed, and its every covariable is the innermost one.
    #[test]
    fn focusing_is_total_on_generated_computations(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let focused = focus_computation(&generated.core, root, &mut arena, &mut provenance);
        prop_assert!(focused.is_ok(), "focusing refused a closed term: {:?}", focused);
        let command = focused.expect("checked above");
        prop_assert_eq!(Ok(FreeSet::default()), check_command(&arena, command), "the image is well formed and closed");
        prop_assert_eq!(Agreement::Same, every_covariable_is_innermost(&arena), "a covariable other than α0 was minted");
    }

    /// Every command of a focused computation carries the support an
    /// independent walk computes: the check's answer, read off the carried
    /// support, is the walked free set at every command, not only the root.
    #[test]
    fn root_support_equals_the_walk_on_every_focused_term(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        focus_computation(&generated.core, root, &mut arena, &mut provenance).expect("focusing is total");
        prop_assert_eq!(Agreement::Same, supports_are_walked(&arena), "a carried support differs from the walk");
    }

    /// Unfocusing reads a focused computation back as the computation it came
    /// from.
    #[test]
    fn unfocusing_inverts_focusing_on_generated_computations(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&generated.core, root, &mut arena, &mut provenance).expect("focusing is total");
        let mut decoded = CoreArena::new();
        let back = unfocus_command(&arena, command, &mut decoded);
        prop_assert!(back.is_ok(), "the image did not decode: {:?}", back);
        prop_assert_eq!(
            Agreement::Same,
            same_computation(&generated.core, root, &decoded, back.expect("checked above")),
            "unfocusing changed the term"
        );
    }

    /// Unfocusing reads a focused value back as the value it came from.
    #[test]
    fn unfocusing_inverts_focusing_on_generated_values(generated in values())
    {
        let GeneratedRoot::Value(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields values"));
        };
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let producer = focus_value(&generated.core, root, &mut arena, &mut provenance).expect("focusing is total");
        let mut decoded = CoreArena::new();
        let back = unfocus_value(&arena, producer, &mut decoded);
        prop_assert!(back.is_ok(), "the image did not decode: {:?}", back);
        prop_assert_eq!(
            Agreement::Same,
            same_value(&generated.core, root, &decoded, back.expect("checked above")),
            "unfocusing changed the value"
        );
    }
}

/// A core node a support is read at, in its family.
#[derive(Clone, Copy, Debug)]
enum Subject
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// A node in a family the syntactic comparisons read: a computation or a
/// value as a thunk, a computation type as a thunk type.
#[derive(Clone, Copy, Debug)]
enum Compared
{
    /// A value.
    Value(ValueId),
    /// A value type.
    Type(ValueTypeId),
}

/// `subject` as the syntactic comparisons read it.
///
/// # Specification
/// trivial.
fn compared(
    arena: &mut CoreArena,
    subject: Subject,
) -> Compared
{
    match subject {
        Subject::Value(value) => {
            let returned = arena.computation_return(value);
            Compared::Value(arena.value_thunk(returned))
        },
        Subject::Computation(computation) => Compared::Value(arena.value_thunk(computation)),
        Subject::ValueType(ty) => Compared::Type(ty),
        Subject::CompType(ty) => Compared::Type(arena.value_type_thunk(ty)),
    }
}

/// `subject` with every free intuitionistic index at or past `scope` raised
/// by one, as the syntactic comparisons read it.
///
/// # Specification
/// trivial.
fn raised(
    arena: &mut CoreArena,
    subject: Subject,
    scope: Binders,
) -> Compared
{
    let computation = match subject {
        Subject::Value(value) => arena.computation_return(value),
        Subject::Computation(computation) => computation,
        Subject::ValueType(ty) => {
            let shifted = shift_value_type_under(arena, ty, scope, Binders::ONE).settle(arena);
            return Compared::Type(shifted);
        },
        Subject::CompType(ty) => {
            let shifted = shift_comp_type_under(arena, ty, scope, Binders::ONE).settle(arena);
            return Compared::Type(arena.value_type_thunk(shifted));
        },
    };
    let shifted = shift_computation_under(arena, computation, scope, Binders::ONE).settle(arena);
    Compared::Value(arena.value_thunk(shifted))
}

/// Whether two compared nodes are syntactically equal.
///
/// # Specification
/// trivial.
fn same(
    arena: &CoreArena,
    left: Compared,
    right: Compared,
) -> CertificateEquality
{
    match (left, right) {
        (Compared::Value(left), Compared::Value(right)) => {
            equal_certificate_syntax(arena, left, right)
        },
        (Compared::Type(left), Compared::Type(right)) => equal_type_syntax(arena, left, right),
        (Compared::Value(_), Compared::Type(_)) | (Compared::Type(_), Compared::Value(_)) => {
            CertificateEquality::Different
        },
    }
}

/// Whether an index occurs free in a subject.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Occurrence
{
    /// Some occurrence names the index.
    Free,
    /// None does.
    Absent,
}

/// Whether the intuitionistic index `index` occurs free in `subject`, by the
/// shift machine alone: raising the indices at or past `index` and raising
/// those past it differ exactly at an occurrence of it.
///
/// # Specification
/// - requires: `subject` is live in `arena`.
/// - ensures: [`Occurrence::Free`] exactly when an occurrence in `subject`
///   names `index` past the binders between it and the subject; `arena` only
///   grows.
/// - panics: none.
/// - executable: none — the reference the carried core supports are held to,
///   sharing no code with them.
///
/// # Adequacy
/// - hypothesis: L2 — agreement with the carried supports on every node of
///   every generated term.
/// - witness: `tests::focus_properties::core_supports_equal_the_shift_machine_on_every_generated_term`
fn occurs(
    arena: &mut CoreArena,
    subject: Subject,
    index: DeBruijnIndex,
) -> Occurrence
{
    let scope = Binders::from(u32::from(index));
    let at = raised(arena, subject, scope);
    let past = raised(arena, subject, scope.deeper());
    match same(arena, at, past) {
        CertificateEquality::Equal => Occurrence::Absent,
        CertificateEquality::Different => Occurrence::Free,
    }
}

/// Whether every node of `core` carries, in its intuitionistic zone, exactly
/// the indices the shift machine finds free in it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: Same exactly when, at every node of every family, an index up to
///   one past the support's largest is selected exactly when [`occurs`] finds
///   it free, and raising past that changes nothing.
/// - panics: on a node the arena does not hold.
/// - executable: none — the observation of the witness below.
///
/// # Adequacy
/// - hypothesis: L2 — generated terms over every former the generator emits.
/// - witness: `tests::focus_properties::core_supports_equal_the_shift_machine_on_every_generated_term`
fn core_supports_are_walked(core: &CoreArena) -> Agreement
{
    let start = ArenaWatermark::default();
    let subjects: Vec<(Subject, Vec<u32>)> = core
        .values_since(start)
        .map(|id| (Subject::Value(id), core.value_support(id)))
        .chain(
            core.computations_since(start)
                .map(|id| (Subject::Computation(id), core.computation_support(id))),
        )
        .chain(
            core.value_types_since(start)
                .map(|id| (Subject::ValueType(id), core.value_type_support(id))),
        )
        .chain(
            core.comp_types_since(start)
                .map(|id| (Subject::CompType(id), core.comp_type_support(id))),
        )
        .map(|(subject, support)| {
            let selected = support
                .expect("a minted node carries a support")
                .indices(Zone::Intuitionistic)
                .map(u32::from)
                .collect();
            (subject, selected)
        })
        .collect();
    let mut scratch = core.clone();
    let mut walked: Vec<u32> = Vec::new();
    for (subject, selected) in subjects {
        let bound = selected.last().map_or(0, |&last| last.saturating_add(2));
        walked.clear();
        walked.extend((0 .. bound).filter(|&index| {
            occurs(&mut scratch, subject, DeBruijnIndex::from(index)) == Occurrence::Free
        }));
        let original = compared(&mut scratch, subject);
        let beyond = raised(&mut scratch, subject, Binders::from(bound));
        if walked != selected || same(&scratch, original, beyond) == CertificateEquality::Different
        {
            return Agreement::Differ;
        }
    }
    Agreement::Same
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Every node of a generated term carries the support the shift machine
    /// finds: an index is selected exactly when raising the indices at or past
    /// it and raising those past it differ.
    #[test]
    fn core_supports_equal_the_shift_machine_on_every_generated_term(generated in computations())
    {
        prop_assert_eq!(
            Agreement::Same,
            core_supports_are_walked(&generated.core),
            "a carried core support differs from the shift machine"
        );
    }
}

/// One hand-built case: its label, term, and root command's origin.
struct Case
{
    /// What the case exercises.
    label: &'static str,
    /// The arena the term lives in.
    core: CoreArena,
    /// The term.
    root: ComputationId,
    /// The origin focusing records for the root command.
    origin: FocusOrigin,
}

/// The hand-built cases, one per former and one per naming rule.
///
/// # Specification
/// trivial.
fn cases() -> Vec<Case>
{
    let mut cases = Vec::new();

    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let root = core.computation_return(seven);
    cases.push(Case {
        label: "return",
        core,
        root,
        origin: FocusOrigin::Return,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let body = core.computation_return(unit);
    let thunk = core.value_thunk(body);
    let root = core.computation_force(thunk);
    cases.push(Case {
        label: "force a thunk",
        core,
        root,
        origin: FocusOrigin::Force,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let body = core.computation_return(variable);
    let lambda = core.computation_lambda(body);
    let root = core.computation_application(lambda, unit);
    cases.push(Case {
        label: "apply a lambda",
        core,
        root,
        origin: FocusOrigin::Lambda,
    });

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let head = core.computation_return(one);
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let body = core.computation_return(variable);
    let root = core.computation_bind(head, body);
    cases.push(Case {
        label: "bind under a tail",
        core,
        root,
        origin: FocusOrigin::Return,
    });

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let unit = core.value_unit();
    let head = core.computation_return(one);
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let inner = core.computation_return(outer);
    let function = core.computation_lambda(inner);
    let bound = core.computation_bind(head, function);
    let root = core.computation_application(bound, unit);
    cases.push(Case {
        label: "bind under a frame",
        core,
        root,
        origin: FocusOrigin::Bind,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let scrutinee = core.value_injection(Side::Left.into(), unit);
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let on_left = core.computation_return(one);
    let on_right = core.computation_return(two);
    let root = core.computation_case(scrutinee, &[on_left, on_right]);
    cases.push(Case {
        label: "case under a tail",
        core,
        root,
        origin: FocusOrigin::Case,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let scrutinee = core.value_injection(Side::Left.into(), unit);
    let own = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let left_body = core.computation_return(own);
    let on_left = core.computation_lambda(left_body);
    let five = integer(&mut core, Integer(5));
    let right_body = core.computation_return(five);
    let on_right = core.computation_lambda(right_body);
    let cased = core.computation_case(scrutinee, &[on_left, on_right]);
    let three = integer(&mut core, Integer(3));
    let root = core.computation_application(cased, three);
    cases.push(Case {
        label: "case under a frame",
        core,
        root,
        origin: FocusOrigin::Case,
    });

    let mut core = CoreArena::new();
    let constant = core.value_constant(ConstantIndex::from(0_usize));
    let minus_three = integer(&mut core, Integer(-3));
    let lifted = core.value_lift(Level::zero(), minus_three);
    let pair = core.value_tuple(&[constant, lifted]);
    let root = core.computation_return(pair);
    cases.push(Case {
        label: "structured values",
        core,
        root,
        origin: FocusOrigin::Return,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let triple = core.value_tuple(&[one, unit, two]);
    let scrutinee = core.value_injection(Summand::from(2_usize), triple);
    let on_first = core.computation_return(one);
    let on_second = core.computation_return(two);
    let own = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let on_third = core.computation_return(own);
    let root = core.computation_case(scrutinee, &[on_first, on_second, on_third]);
    cases.push(Case {
        label: "a third summand of a triple, cased three ways",
        core,
        root,
        origin: FocusOrigin::Case,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let triple = core.value_tuple(&[one, unit, two]);
    let middle = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let body = core.computation_return(middle);
    let root = core.computation_split(triple, ComponentCount::from(3_usize), body);
    cases.push(Case {
        label: "a triple split, its middle component returned",
        core,
        root,
        origin: FocusOrigin::Case,
    });

    let mut core = CoreArena::new();
    let discarded = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let three = integer(&mut core, Integer(3));
    let body = core.computation_return(three);
    let split = core.computation_split(discarded, ComponentCount::default(), body);
    let root = core.computation_lambda(split);
    cases.push(Case {
        label: "an empty split under a lambda",
        core,
        root,
        origin: FocusOrigin::Lambda,
    });

    let mut core = CoreArena::new();
    let absurd = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let empty = core.computation_case(absurd, &[]);
    let root = core.computation_lambda(empty);
    cases.push(Case {
        label: "an empty case",
        core,
        root,
        origin: FocusOrigin::Lambda,
    });

    let mut core = CoreArena::new();
    let nat = core.value_type_data(ConstantIndex::from(1_usize), alloc::vec![]);
    let seven = integer(&mut core, Integer(7));
    let scrutinee = core.value_constructor(nat, 1_usize.into(), alloc::vec![seven]);
    let returned_type = core.value_type_unit();
    let motive = core.comp_type_returner(returned_type);
    let one = integer(&mut core, Integer(1));
    let on_zero = core.computation_return(one);
    let field = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let field_returned = core.computation_return(field);
    let on_successor = core.computation_lambda(field_returned);
    let root = core.computation_data_case(
        scrutinee,
        motive,
        alloc::vec![on_zero, on_successor],
        [0_usize, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    cases.push(Case {
        label: "nominal match on a datatype constructor",
        core,
        root,
        origin: FocusOrigin::Case,
    });

    let mut core = CoreArena::new();
    let nat = core.value_type_data(ConstantIndex::from(1_usize), alloc::vec![]);
    let zero = core.value_constructor(nat, 0_usize.into(), alloc::vec![]);
    let one = core.value_constructor(nat, 1_usize.into(), alloc::vec![zero]);
    let returned_type = core.value_type_unit();
    let motive = core.comp_type_returner(returned_type);
    let base = core.computation_return(zero);
    let own = core.value_variable(Zone::Intuitionistic, 2_u32.into());
    let predecessor = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let recurse = core.computation_force(own);
    let descent = core.computation_application(recurse, predecessor);
    let step = core.computation_lambda(descent);
    let argument = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let matched = core.computation_data_case(
        argument,
        motive,
        alloc::vec![base, step],
        [0_usize, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let function = core.computation_lambda(matched);
    let recursive = core.computation_fixpoint(
        function,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let root = core.computation_application(recursive, one);
    cases.push(Case {
        label: "a recursive thunk applied",
        core,
        root,
        origin: FocusOrigin::Fixpoint,
    });

    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let record = core.value_record(alloc::collections::BTreeMap::from([
        (label("c"), unit),
        (label("a"), one),
        (label("b"), two),
    ]));
    let root = core.computation_return(record);
    cases.push(Case {
        label: "a record of three labels returned",
        core,
        root,
        origin: FocusOrigin::Return,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let record = core.value_record(alloc::collections::BTreeMap::from([
        (label("a"), one),
        (label("b"), unit),
        (label("c"), two),
    ]));
    let root = core.computation_record_projection(record, label("b"));
    cases.push(Case {
        label: "a record of three labels, its middle label projected",
        core,
        root,
        origin: FocusOrigin::Projection,
    });

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let triple = core.value_tuple(&[one, unit, two]);
    let projected = core.computation_tuple_projection(triple, 1_usize.into());
    let own = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let body = core.computation_return(own);
    let root = core.computation_bind(projected, body);
    cases.push(Case {
        label: "a triple's middle component projected and bound",
        core,
        root,
        origin: FocusOrigin::Projection,
    });

    cases
}

/// Each pure former records its origin, passes the scope check closed, and
/// reads back as itself; together the cases record the pure computation
/// origins.
#[test]
fn hand_built_cases_cover_every_former()
{
    let mut seen = BTreeSet::new();
    for case in cases() {
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&case.core, case.root, &mut arena, &mut provenance)
            .unwrap_or_else(|refusal| panic!("{}: focusing refused: {refusal}", case.label));
        assert_eq!(
            Some(case.origin),
            provenance.origin(command),
            "{}: the root's origin",
            case.label
        );
        assert_eq!(
            Ok(FreeSet::default()),
            check_command(&arena, command),
            "{}: the image is well formed and closed",
            case.label
        );
        assert_eq!(
            Agreement::Same,
            supports_are_walked(&arena),
            "{}: every command carries its walked support",
            case.label
        );
        let mut decoded = CoreArena::new();
        let back = unfocus_command(&arena, command, &mut decoded)
            .unwrap_or_else(|refusal| panic!("{}: unfocusing refused: {refusal}", case.label));
        assert_eq!(
            Agreement::Same,
            same_computation(&case.core, case.root, &decoded, back),
            "{}: the round trip",
            case.label
        );
        seen.extend(provenance.entries().map(|(_, origin)| origin));
    }
    assert_eq!(
        BTreeSet::from([
            FocusOrigin::Return,
            FocusOrigin::Force,
            FocusOrigin::Fixpoint,
            FocusOrigin::Lambda,
            FocusOrigin::Case,
            FocusOrigin::Projection,
            FocusOrigin::Bind,
        ]),
        seen,
        "every computation origin is exercised"
    );
}

/// A declaration's value focuses to one positive cut against `★`, recorded
/// as a top value.
#[test]
fn top_level_value_focuses_against_top()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let command =
        focus_top_value(&core, seven, &mut arena, &mut provenance).expect("a literal focuses");
    assert_eq!(
        Some(FocusOrigin::TopValue),
        provenance.origin(command),
        "recorded as a top value"
    );
    assert_eq!(
        Ok(FreeSet::default()),
        check_command(&arena, command),
        "well formed and closed"
    );
}

/// Every consumer counts, not only the consumers reached from a selected
/// command.
#[test]
fn covariable_observation_includes_unreachable_nodes()
{
    let mut arena = CommandArena::new();
    assert_eq!(Agreement::Same, every_covariable_is_innermost(&arena));
    arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    assert_eq!(Agreement::Same, every_covariable_is_innermost(&arena));
    arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("leaf");
    assert_eq!(Agreement::Same, every_covariable_is_innermost(&arena));
    arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(1_u32)))
        .expect("leaf");
    assert_eq!(Agreement::Differ, every_covariable_is_innermost(&arena));
}
