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
