use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::OperationNode;
use gandr_kernel_term::OperationRule;
use gandr_kernel_term::OperationRuleFault;
use gandr_kernel_term::OperationRuleRefusal;
use gandr_kernel_term::OperationRules;
use gandr_kernel_term::Overlapped;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::RuleVariable;

use crate::env::Environment;
use crate::error::KernelError;
use crate::ruled::OperationBodyFault;

/// `or` at position `$constant` over the booleans at 0.
macro_rules! or {
    ($constant:expr) => {
        OperationNode::Operation {
            constant: ConstantIndex::from($constant),
            arity: FieldCount::from(2_usize),
        }
    };
}

/// The boolean constructor `$tag`: `False` is 0, `True` is 1.
macro_rules! boolean {
    ($tag:expr) => {
        OperationNode::Constructor {
            family: ConstantIndex::from(0_usize),
            tag: ConstructorTag::from($tag),
        }
    };
}

/// `False`'s tag.
const FALSE: usize = 0;
/// `True`'s tag.
const TRUE: usize = 1;

/// Pattern variable `$ordinal`.
macro_rules! var {
    ($ordinal:expr) => {
        OperationNode::Variable(RuleVariable::from($ordinal))
    };
}

/// Admit a definition at the next position carrying `rules`, its body the
/// unit: only a system the kernel refuses before its body is read.
///
/// # Specification
/// trivial.
fn admit(
    environment: &mut Environment,
    rules: Vec<OperationRule>,
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let unit_type = staging.arena().value_type_unit();
    let unit = staging.arena().value_unit();
    let declaration = staging
        .def(LevelSignature::monomorphic(), unit_type, unit)
        .ruled(OperationRules::new(rules));
    environment.add_decl(declaration).map(|_admitted| ())
}

/// Admit `or` over the booleans at 0, carrying `rules`, as the tree the
/// lowering compiles its three rules to: a case on the first input whose
/// `False` branch cases on the second. `leaves` are the constructors the
/// leaves return: `or(False, False)`, `or(False, True)`, `or(True, _)`.
///
/// # Specification
/// trivial.
fn admit_or(
    environment: &mut Environment,
    rules: Vec<OperationRule>,
    leaves: [ConstructorTag; 3],
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let booleans = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let motive = arena.comp_type_returner(booleans);
    let [false_false, false_true, true_any] = leaves.map(|tag| {
        let constructed = arena.value_constructor(booleans, tag, vec![]);
        arena.computation_return(constructed)
    });
    let second = arena.value_variable(DeBruijnIndex::from(0_u32));
    let on_second = arena.computation_data_case(second, motive, vec![false_false, false_true]);
    let first = arena.value_variable(DeBruijnIndex::from(1_u32));
    let tree = arena.computation_data_case(first, motive, vec![on_second, true_any]);
    let inner = arena.computation_lambda(tree);
    let outer = arena.computation_lambda(inner);
    let fixpoint = arena.computation_fixpoint(outer, FixpointEvidence::Partial);
    let body = arena.value_thunk(fixpoint);
    let codomain = arena.comp_type_arrow(booleans, motive);
    let signature = arena.comp_type_arrow(booleans, codomain);
    let declared = arena.value_type_thunk(signature);
    let declaration = staging
        .def(LevelSignature::monomorphic(), declared, body)
        .ruled(OperationRules::new(rules));
    environment.add_decl(declaration).map(|_admitted| ())
}

#[test]
fn rules_over_the_environment_admit_and_a_forged_pair_is_refused()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let booleans = staging.data(
        LevelSignature::monomorphic(),
        vec![],
        vec![vec![], vec![]],
        kind,
    );
    let _booleans = environment.add_decl(booleans).expect("the booleans admit");
    let rule = |left: &[OperationNode], right: &[OperationNode]| {
        OperationRule::new(Box::from(left), Box::from(right))
    };
    // `or(True, x) ==> True` and `or(x, True) ==> True` overlap at
    // `or(True, True)`, where both give `True`.
    let joined = vec![
        rule(&[or!(1_usize), boolean!(TRUE), var!(0_u32)], &[boolean!(
            TRUE
        )]),
        rule(&[or!(1_usize), var!(0_u32), boolean!(TRUE)], &[boolean!(
            TRUE
        )]),
        rule(&[or!(1_usize), boolean!(FALSE), boolean!(FALSE)], &[
            boolean!(FALSE),
        ]),
    ];
    assert_eq!(
        admit_or(&mut environment, joined, [
            ConstructorTag::from(FALSE),
            ConstructorTag::from(TRUE),
            ConstructorTag::from(TRUE),
        ]),
        Ok(()),
        "the rules converge and the body is their tree"
    );
    // The same overlap forged to part: the kernel computes the pair itself.
    let forged = vec![
        rule(&[or!(2_usize), boolean!(TRUE), var!(0_u32)], &[boolean!(
            TRUE
        )]),
        rule(&[or!(2_usize), var!(0_u32), boolean!(TRUE)], &[boolean!(
            FALSE
        )]),
    ];
    assert_eq!(
        admit(&mut environment, forged),
        Err(KernelError::OperationRulesRefused(OperationRuleRefusal {
            rule: RuleIndex::from(1_usize),
            fault: OperationRuleFault::Diverges(Overlapped::Operation(RuleIndex::from(0_usize))),
        })),
        "`or(True, True)` rewrites to two normal forms"
    );
    // A rule calling past its own position names nothing admitted.
    let later = vec![rule(&[or!(2_usize), var!(0_u32), var!(1_u32)], &[
        or!(3_usize),
        var!(0_u32),
        var!(1_u32),
    ])];
    assert_eq!(
        admit(&mut environment, later),
        Err(KernelError::OperationRulesRefused(OperationRuleRefusal {
            rule: RuleIndex::from(0_usize),
            fault: OperationRuleFault::UnknownOperation,
        })),
        "an operation calls only itself and ruled definitions before it"
    );
}

#[test]
fn a_body_is_admitted_only_as_its_rules_decision_tree()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let booleans = staging.data(
        LevelSignature::monomorphic(),
        vec![],
        vec![vec![], vec![]],
        kind,
    );
    let _booleans = environment.add_decl(booleans).expect("the booleans admit");
    let rules = |position: usize| {
        let rule = |left: &[OperationNode], right: &[OperationNode]| {
            OperationRule::new(Box::from(left), Box::from(right))
        };
        vec![
            rule(&[or!(position), boolean!(TRUE), var!(0_u32)], &[boolean!(
                TRUE
            )]),
            rule(&[or!(position), var!(0_u32), boolean!(TRUE)], &[boolean!(
                TRUE
            )]),
            rule(&[or!(position), boolean!(FALSE), boolean!(FALSE)], &[
                boolean!(FALSE),
            ]),
        ]
    };
    let [no, yes] = [FALSE, TRUE].map(ConstructorTag::from);
    // `or(False, True)` is `True` by the second rule; a body answering
    // `False` there computes something the rules do not.
    assert_eq!(
        admit_or(&mut environment, rules(1), [no, no, yes]),
        Err(KernelError::OperationBodyUnlinked(
            OperationBodyFault::Apart(RuleIndex::from(1_usize))
        )),
        "the leaf is not its rule's right side"
    );
    assert_eq!(
        admit(&mut environment, rules(1)),
        Err(KernelError::OperationBodyUnlinked(
            OperationBodyFault::Shape
        )),
        "a body that is no fixpoint over the inputs is no decision tree"
    );
    assert_eq!(
        admit_or(&mut environment, rules(1), [no, yes, yes]),
        Ok(()),
        "the tree the lowering compiles is admitted"
    );
}

/// `add` at `$constant` over the naturals at 0.
macro_rules! add {
    ($constant:expr) => {
        OperationNode::Operation {
            constant: ConstantIndex::from($constant),
            arity: FieldCount::from(2_usize),
        }
    };
}

/// The natural constructor `$tag`: `zero` is 0, `succ` is 1.
macro_rules! natural {
    ($tag:expr) => {
        OperationNode::Constructor {
            family: ConstantIndex::from(0_usize),
            tag: ConstructorTag::from($tag),
        }
    };
}

/// `zero`'s tag.
const ZERO: usize = 0;
/// `succ`'s tag.
const SUCC: usize = 1;

/// Where `add`'s recursive call stands in its `succ` rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Recursion
{
    /// `add(succ x, y) ==> succ(add(x, y))`: a call bound below the root.
    Under,
    /// `add(succ x, y) ==> add(x, succ y)`: the call is the root.
    Tail,
}

/// The naturals at 0, `zero` and `succ` over themselves, admitted into a
/// fresh environment.
///
/// # Specification
/// trivial.
fn naturals() -> Environment
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let naturals = staging.data(
        LevelSignature::monomorphic(),
        vec![],
        vec![vec![], vec![own]],
        kind,
    );
    let _naturals = environment.add_decl(naturals).expect("the naturals admit");
    environment
}

/// `add`'s two rules at `position`, its `succ` rule recursing as `recursion`
/// says.
///
/// # Specification
/// trivial.
fn add_rules(
    position: ConstantIndex,
    recursion: Recursion,
) -> Vec<OperationRule>
{
    let position = usize::from(position);
    let rule = |left: &[OperationNode], right: &[OperationNode]| {
        OperationRule::new(Box::from(left), Box::from(right))
    };
    let onward = match recursion {
        Recursion::Under => rule(
            &[add!(position), natural!(SUCC), var!(0_u32), var!(1_u32)],
            &[natural!(SUCC), add!(position), var!(0_u32), var!(1_u32)],
        ),
        Recursion::Tail => rule(
            &[add!(position), natural!(SUCC), var!(0_u32), var!(1_u32)],
            &[add!(position), var!(0_u32), natural!(SUCC), var!(1_u32)],
        ),
    };
    vec![
        rule(&[add!(position), natural!(ZERO), var!(0_u32)], &[var!(
            0_u32
        )]),
        onward,
    ]
}

/// How a body offered for `add` departs from its rules' tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Departure
{
    /// The tree itself.
    Kept,
    /// The `zero` leaf returns `zero` rather than `y`.
    Leaf,
    /// The `succ` branch is `(force rec) x`, no lambda over its field.
    Branch,
    /// The fixpoint's body is `force rec`, no lambda over the inputs.
    Inputs,
    /// `thunk (λx y. return y)`: no fixpoint.
    Fixpoint,
}

/// Offer `add` at the next position, `U (Nat → Nat → F Nat)`, carrying its
/// rules, as the tree `thunk (fix rec. λx y. case x of { zero ↦ return y;
/// succ ↦ λp. … })` departs from it as `departure` says.
///
/// # Specification
/// trivial.
fn admit_add(
    environment: &mut Environment,
    recursion: Recursion,
    departure: Departure,
) -> Result<(), KernelError>
{
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let naturals = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let motive = arena.comp_type_returner(naturals);
    let codomain = arena.comp_type_arrow(naturals, motive);
    let signature = arena.comp_type_arrow(naturals, codomain);
    let declared = arena.value_type_thunk(signature);
    // At the `zero` leaf: `y` 0, `x` 1, `rec` 2.
    let on_zero = if departure == Departure::Leaf {
        let zero = arena.value_constructor(naturals, ConstructorTag::from(ZERO), vec![]);
        arena.computation_return(zero)
    }
    else {
        let y = arena.value_variable(DeBruijnIndex::from(0_u32));
        arena.computation_return(y)
    };
    // At the `succ` leaf: `p` 0, `y` 1, `x` 2, `rec` 3.
    let recursive = arena.value_variable(DeBruijnIndex::from(3_u32));
    let forced = arena.computation_force(recursive);
    let p = arena.value_variable(DeBruijnIndex::from(0_u32));
    let y = arena.value_variable(DeBruijnIndex::from(1_u32));
    let on_succ = match recursion {
        Recursion::Under => {
            let on_p = arena.computation_application(forced, p);
            let called = arena.computation_application(on_p, y);
            let result = arena.value_variable(DeBruijnIndex::from(0_u32));
            let after = arena.value_constructor(naturals, ConstructorTag::from(SUCC), vec![result]);
            let returned = arena.computation_return(after);
            arena.computation_bind(called, returned)
        },
        Recursion::Tail => {
            let on_p = arena.computation_application(forced, p);
            let next = arena.value_constructor(naturals, ConstructorTag::from(SUCC), vec![y]);
            arena.computation_application(on_p, next)
        },
    };
    let on_succ = if departure == Departure::Branch {
        // Under `y` 0, `x` 1, `rec` 2: the branch is `(force rec) x`.
        let recursive = arena.value_variable(DeBruijnIndex::from(2_u32));
        let forced = arena.computation_force(recursive);
        let x = arena.value_variable(DeBruijnIndex::from(1_u32));
        arena.computation_application(forced, x)
    }
    else {
        arena.computation_lambda(on_succ)
    };
    let x = arena.value_variable(DeBruijnIndex::from(1_u32));
    let tree = arena.computation_data_case(x, motive, vec![on_zero, on_succ]);
    let inputs = match departure {
        Departure::Inputs => {
            let recursive = arena.value_variable(DeBruijnIndex::from(0_u32));
            arena.computation_force(recursive)
        },
        Departure::Fixpoint => {
            let y = arena.value_variable(DeBruijnIndex::from(0_u32));
            let returned = arena.computation_return(y);
            let inner = arena.computation_lambda(returned);
            arena.computation_lambda(inner)
        },
        Departure::Kept | Departure::Leaf | Departure::Branch => {
            let inner = arena.computation_lambda(tree);
            arena.computation_lambda(inner)
        },
    };
    let body = if departure == Departure::Fixpoint {
        inputs
    }
    else {
        arena.computation_fixpoint(inputs, FixpointEvidence::Partial)
    };
    let body = arena.value_thunk(body);
    let declaration = staging
        .def(LevelSignature::monomorphic(), declared, body)
        .ruled(OperationRules::new(add_rules(position, recursion)));
    environment.add_decl(declaration).map(|_admitted| ())
}

/// A body over a recursive family links its fields and its calls: the tree
/// whose `succ` leaf binds the recursive call below `succ`, and the one
/// whose leaf is the call itself, are each admitted as their rules' tree; a
/// leaf returning another value is apart from its rule, and a body that is
/// no fixpoint, no lambda over the inputs or no lambda over a branch's
/// field is refused for its shape.
#[test]
fn a_recursive_body_links_its_fields_and_calls()
{
    let mut environment = naturals();
    for recursion in [Recursion::Under, Recursion::Tail] {
        assert_eq!(
            admit_add(&mut environment, recursion, Departure::Kept),
            Ok(()),
            "{recursion:?}"
        );
        assert_eq!(
            admit_add(&mut environment, recursion, Departure::Leaf),
            Err(KernelError::OperationBodyUnlinked(
                OperationBodyFault::Apart(RuleIndex::from(0_usize))
            )),
            "{recursion:?}"
        );
        for departure in [Departure::Branch, Departure::Inputs, Departure::Fixpoint] {
            assert_eq!(
                admit_add(&mut environment, recursion, departure),
                Err(KernelError::OperationBodyUnlinked(
                    OperationBodyFault::Shape
                )),
                "{recursion:?}: {departure:?}"
            );
        }
    }
}
