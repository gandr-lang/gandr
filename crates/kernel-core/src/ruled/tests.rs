use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
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
use gandr_kernel_term::SourceRank;
use gandr_kernel_term::Value;
use quenchant_shape::shape::Maybe;

use crate::Environment;
use crate::env::Admission;
use crate::env::CheckedId;
use crate::error::KeepRefusal;
use crate::error::KernelError;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayDecline;
use crate::replay::ReplayNode;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::replay::replay;
use crate::ruled::OperationBodyFault;
use crate::verdict::KernelSigner;
use crate::verdict::NoVerdicts;
use crate::verdict::StoredReceipt;
use crate::verdict::TrustPolicy;
use crate::verdict::VerdictKey;
use crate::verdict::VerdictSource;

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
        let constructed =
            arena.value_constructor(ConstantIndex::from(0_usize), booleans, tag, vec![]);
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
    // A rule calling past its own position names nothing admitted. The forged
    // rules leave a vacancy at 2, so this operation stands at 3.
    let later = vec![rule(&[or!(3_usize), var!(0_u32), var!(1_u32)], &[
        or!(4_usize),
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
    // `False` there computes something the rules do not. Each refused offer
    // leaves a vacancy, so each offer stands one position past the one before.
    assert_eq!(
        admit_or(&mut environment, rules(1), [no, no, yes]),
        Err(KernelError::OperationBodyUnlinked(
            OperationBodyFault::Apart(RuleIndex::from(1_usize))
        )),
        "the leaf is not its rule's right side"
    );
    assert_eq!(
        admit(&mut environment, rules(2)),
        Err(KernelError::OperationBodyUnlinked(
            OperationBodyFault::Shape
        )),
        "a body that is no fixpoint over the inputs is no decision tree"
    );
    assert_eq!(
        admit_or(&mut environment, rules(3), [no, yes, yes]),
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
        let zero = arena.value_constructor(
            ConstantIndex::from(0_usize),
            naturals,
            ConstructorTag::from(ZERO),
            vec![],
        );
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
            let after = arena.value_constructor(
                ConstantIndex::from(0_usize),
                naturals,
                ConstructorTag::from(SUCC),
                vec![result],
            );
            let returned = arena.computation_return(after);
            arena.computation_bind(called, returned)
        },
        Recursion::Tail => {
            let on_p = arena.computation_application(forced, p);
            let next = arena.value_constructor(
                ConstantIndex::from(0_usize),
                naturals,
                ConstructorTag::from(SUCC),
                vec![y],
            );
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

/// The partial gate unfolds the fixpoint of a ruled definition. At the
/// unfoldings that rule the admission log, `add(succ zero, zero)` replays as
/// `return succ zero` through its recursive call. At the unfoldings without
/// the ruling, the same pair declines at the gate.
#[test]
fn a_ruled_fixpoint_unfolds_at_its_partial_gate_4291()
{
    let mut environment = naturals();
    assert_eq!(
        admit_add(&mut environment, Recursion::Under, Departure::Kept),
        Ok(())
    );
    let mut arena = environment.arena().clone();
    let entries = environment.entries();
    let root = entries
        .iter()
        .find_map(|entry| {
            if let DeclarationContent::Def { body, .. } = *entry.content()
                && let Some(&Value::Thunk(root)) = arena.value(body)
            {
                Some(root)
            }
            else {
                None
            }
        })
        .expect("`add` thunks its fixpoint");
    let naturals = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let family = ConstantIndex::from(0_usize);
    let zero = arena.value_constructor(family, naturals, ConstructorTag::from(ZERO), vec![]);
    let one = arena.value_constructor(family, naturals, ConstructorTag::from(SUCC), vec![zero]);
    let on_x = arena.computation_application(root, one);
    let called = arena.computation_application(on_x, zero);
    let expected = arena.computation_return(one);
    for (unfoldings, verdict) in [
        (
            Unfoldings::default().ruling(entries),
            KernelVerdict::Convertible,
        ),
        (
            Unfoldings::default(),
            KernelVerdict::Declined(ReplayDecline::PartialFixpoint),
        ),
    ] {
        assert_eq!(
            replay(
                &mut arena,
                &unfoldings,
                ReplaySides::Computations(called, expected),
                EngineClaim::Convertible,
                [ConversionDecision::ComparedShared {
                    left: ReplayNode::Other,
                    right: ReplayNode::Other,
                }],
                ReplayBudget::default(),
            ),
            verdict
        );
    }
}

/// The unary operation at `$constant` over the booleans at 0.
macro_rules! unary {
    ($constant:expr) => {
        OperationNode::Operation {
            constant: ConstantIndex::from($constant),
            arity: FieldCount::from(1_usize),
        }
    };
}

/// `environment`, empty, with the booleans at 0, `False` and `True`.
///
/// # Specification
/// trivial.
fn booleans(mut environment: Environment) -> Environment
{
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
    environment
}

/// Admit, at the next position and ranked at `rank`, the identity on the
/// booleans as a ruled operation: `f(False) ==> False` and `f(True) ==>
/// True`, with the laws `laws` gives for its own position beside them.
///
/// # Specification
/// trivial.
fn admit_identity(
    environment: &mut Environment,
    rank: SourceRank,
    laws: impl Fn(ConstantIndex) -> Vec<OperationRule>,
) -> Result<(), KernelError>
{
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let booleans = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let motive = arena.comp_type_returner(booleans);
    let [on_false, on_true] = [FALSE, TRUE].map(|tag| {
        let constructed = arena.value_constructor(
            ConstantIndex::from(0_usize),
            booleans,
            ConstructorTag::from(tag),
            vec![],
        );
        arena.computation_return(constructed)
    });
    let x = arena.value_variable(DeBruijnIndex::from(0_u32));
    let tree = arena.computation_data_case(x, motive, vec![on_false, on_true]);
    let inputs = arena.computation_lambda(tree);
    let fixpoint = arena.computation_fixpoint(inputs, FixpointEvidence::Partial);
    let body = arena.value_thunk(fixpoint);
    let signature = arena.comp_type_arrow(booleans, motive);
    let declared = arena.value_type_thunk(signature);
    let rule = |left: &[OperationNode], right: &[OperationNode]| {
        OperationRule::new(Box::from(left), Box::from(right))
    };
    let mut rules = vec![
        rule(&[unary!(position), boolean!(FALSE)], &[boolean!(FALSE)]),
        rule(&[unary!(position), boolean!(TRUE)], &[boolean!(TRUE)]),
    ];
    rules.extend(laws(position));
    let declaration = staging
        .def(LevelSignature::monomorphic(), declared, body)
        .ruled(OperationRules::new(rules))
        .ranked(rank);
    environment.add_decl(declaration).map(|_admitted| ())
}

/// The path order places an operation at its source rank, not at its
/// position. The source holds `a`, `b` and `c`, each the identity on the
/// booleans as a ruled operation, and `c` carries the law `c(a(x)) ==>
/// c(b(x))`, which orients only when `a` ranks above `b`. A fresh admission
/// ranks `b` above `a` and refuses the law. The second environment admits
/// `b` before `a` but ranks each where the source states it, so it must
/// refuse the law too, though `a` stands at the later position.
#[test]
fn a_rank_below_an_earlier_admission_orients_as_admitted_before_it_6621()
{
    let law = |left: usize, right: usize| {
        move |own: ConstantIndex| {
            vec![OperationRule::new(
                Box::from([unary!(own), unary!(left), var!(0_u32)].as_slice()),
                Box::from([unary!(own), unary!(right), var!(0_u32)].as_slice()),
            )]
        }
    };
    let plain = |_own: ConstantIndex| Vec::new();
    let rank = |place: usize| SourceRank::from(place);
    // In source order: `a` at 1, `b` at 2, `c` at 3, each ranked at its
    // position.
    let mut fresh = booleans(Environment::new());
    assert_eq!(
        admit_identity(&mut fresh, rank(1), plain),
        Ok(()),
        "`a` admits"
    );
    assert_eq!(
        admit_identity(&mut fresh, rank(2), plain),
        Ok(()),
        "`b` admits"
    );
    let fresh_law = admit_identity(&mut fresh, rank(3), law(1, 2));
    // Out of source order: `b` at 1 ranked 2, `a` at 2 ranked 1, then `c`.
    let mut ranked = booleans(Environment::new());
    assert_eq!(
        admit_identity(&mut ranked, rank(2), plain),
        Ok(()),
        "`b` admits"
    );
    assert_eq!(
        admit_identity(&mut ranked, rank(1), plain),
        Ok(()),
        "`a` admits"
    );
    let ranked_law = admit_identity(&mut ranked, rank(3), law(2, 1));
    assert_eq!(
        fresh_law,
        Err(KernelError::OperationRulesRefused(OperationRuleRefusal {
            rule: RuleIndex::from(2_usize),
            fault: OperationRuleFault::Unoriented,
        })),
        "a fresh admission refuses the law"
    );
    assert_eq!(
        ranked_law, fresh_law,
        "the ranks, not the positions, orient the law"
    );
}

/// A fresh environment that keys each admission, so a readmission can keep
/// an entry on its key.
///
/// # Specification
/// trivial.
fn keyed() -> Environment
{
    let signer = KernelSigner::from([7_u8; 32]);
    Environment::recalling(
        TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
        Arc::new(NoVerdicts),
    )
}

/// A readmission that keeps an entry and appends the reach of an edit
/// orients a law as a fresh admission of the edited source does. The source
/// holds `a`, `b` and `c`, each the identity on the booleans as a ruled
/// operation. The edit touches `a`, and it gives `c` the law `c(a(x)) ==>
/// c(b(x))`, which orients only when `a` ranks above `b`. A fresh admission
/// ranks `b` above `a` and refuses the law. The readmission retires `a`, `b`
/// and `c`, offers `a` again at rank 1, keeps `b` at rank 2 and offers `c`
/// at rank 3. The new `a` stands at a later position than `b`, but the law
/// is refused, as the fresh admission refuses it.
#[test]
fn an_appended_reach_orients_a_law_as_a_fresh_admission_does_6621()
{
    let law = |left: usize, right: usize| {
        move |own: ConstantIndex| {
            vec![OperationRule::new(
                Box::from([unary!(own), unary!(left), var!(0_u32)].as_slice()),
                Box::from([unary!(own), unary!(right), var!(0_u32)].as_slice()),
            )]
        }
    };
    let plain = |_own: ConstantIndex| Vec::new();
    let rank = SourceRank::from;
    let at = ConstantIndex::from;
    let mut fresh = booleans(keyed());
    for place in [1_usize, 2] {
        assert_eq!(
            admit_identity(&mut fresh, rank(place), plain),
            Ok(()),
            "the fresh operations admit"
        );
    }
    let fresh_law = admit_identity(&mut fresh, rank(3_usize), law(1, 2));
    // The previous revision: `a` at 1, `b` at 2 and `c` at 3, `c` with no
    // law.
    let mut readmitted = booleans(keyed());
    for place in [1_usize, 2, 3] {
        assert_eq!(
            admit_identity(&mut readmitted, rank(place), plain),
            Ok(()),
            "the previous revision admits"
        );
    }
    let watermark = readmitted.arena().watermark();
    assert_eq!(
        readmitted.retire(&[at(1_usize), at(2_usize), at(3_usize)]),
        Ok(()),
        "the readmission retires `a`, `b` and `c`"
    );
    assert_eq!(
        readmitted.arena().watermark(),
        watermark,
        "the retire mints nothing"
    );
    assert_eq!(
        admit_identity(&mut readmitted, rank(1_usize), plain),
        Ok(()),
        "`a` admits again, at position 4"
    );
    let watermark = readmitted.arena().watermark();
    assert_eq!(
        readmitted
            .keep((at(2_usize), &[rank(2_usize)]))
            .map(CheckedId::position),
        Ok(at(2_usize)),
        "`b` is kept at position 2"
    );
    assert_eq!(
        readmitted.arena().watermark(),
        watermark,
        "the keep mints nothing"
    );
    let readmitted_law = admit_identity(&mut readmitted, rank(3_usize), law(4, 2));
    assert_eq!(
        fresh_law,
        Err(KernelError::OperationRulesRefused(OperationRuleRefusal {
            rule: RuleIndex::from(2_usize),
            fault: OperationRuleFault::Unoriented,
        })),
        "a fresh admission refuses the law"
    );
    assert_eq!(
        readmitted_law, fresh_law,
        "the readmission refuses the law as the fresh admission does"
    );
}

/// A keep is refused when the precedence that the entry's check reads
/// changed. `c` carries the law `c(a(x)) ==> b(x)`, which orients under
/// either order of `a` and `b`. An edit swaps `a` and `b` in the source. The
/// readmission keeps each of them at its new rank. The key of `c` holds the
/// rank order of the operations its rules name, so the keep of `c` is
/// refused and `c` stays retired. Offered again, `c` admits.
#[test]
fn a_keep_whose_precedence_changed_is_refused_6621()
{
    let law = |left: usize, right: usize| {
        move |own: ConstantIndex| {
            vec![OperationRule::new(
                Box::from([unary!(own), unary!(left), var!(0_u32)].as_slice()),
                Box::from([unary!(right), var!(0_u32)].as_slice()),
            )]
        }
    };
    let plain = |_own: ConstantIndex| Vec::new();
    let rank = SourceRank::from;
    let at = ConstantIndex::from;
    let mut environment = booleans(keyed());
    for place in [1_usize, 2] {
        assert_eq!(
            admit_identity(&mut environment, rank(place), plain),
            Ok(()),
            "`a` and `b` admit"
        );
    }
    assert_eq!(
        admit_identity(&mut environment, rank(3_usize), law(1, 2)),
        Ok(()),
        "`c` admits"
    );
    assert_eq!(
        environment.retire(&[at(1_usize), at(2_usize), at(3_usize)]),
        Ok(()),
        "the readmission retires `a`, `b` and `c`"
    );
    // The edit puts `b` first: `b` at rank 1, `a` at rank 2.
    for (position, place) in [(2_usize, 1_usize), (1, 2)] {
        assert_eq!(
            environment
                .keep((at(position), &[rank(place)]))
                .map(CheckedId::position),
            Ok(at(position)),
            "an operation whose rules name only itself is kept at its new rank"
        );
    }
    assert_eq!(
        environment.keep((at(3_usize), &[rank(3_usize)])),
        Err(KernelError::Unkept {
            position: at(3_usize),
            refusal: KeepRefusal::KeyChanged,
        }),
        "the precedence of what `c` names changed"
    );
    assert!(
        environment.entries().get(3_usize).is_none(),
        "`c` stays retired"
    );
    assert_eq!(
        admit_identity(&mut environment, rank(3_usize), law(1, 2)),
        Ok(()),
        "offered again, `c` admits"
    );
    assert_eq!(
        environment
            .entries()
            .get(4_usize)
            .map(crate::env::AdmittedDeclaration::admission),
        Some(Admission::Checked),
        "the kernel checks the offered `c`"
    );
}

/// A source of verdicts that answers one receipt for every key.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[repr(transparent)]
struct Kept(Vec<Arc<StoredReceipt>>);

impl VerdictSource for Kept
{
    /// The kept receipt, whatever `key` is.
    ///
    /// # Specification
    /// trivial.
    fn receipts(
        &self,
        _key: VerdictKey,
    ) -> &[Arc<StoredReceipt>]
    {
        &self.0
    }
}

/// The ruled twin of `tests::verdicts::a_key_reads_no_admission_order_6568`:
/// the path order compares the ranks of the operations a rule names, so the
/// key of a ruled definition holds their rank order. `a` and `b` are the
/// identity on the booleans at 1 and 2, and `c` carries the law `c(a(x)) ==>
/// b(x)`, which orients under either order of the two. From the receipt of a
/// run in order, a second run in order recalls each declaration. A run that
/// swaps the ranks of `a` and `b` keeps every position and every content, so
/// it recalls `a` and `b`, and checks `c`.
#[test]
fn a_ruled_definition_is_keyed_by_the_rank_order_of_what_it_names_6621()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let trusting = || TrustPolicy::Trusted(BTreeSet::from([signer.identity()]));
    let rank = SourceRank::from;
    let plain = |_own: ConstantIndex| Vec::new();
    let law = |own: ConstantIndex| {
        vec![OperationRule::new(
            Box::from([unary!(own), unary!(1_usize), var!(0_u32)].as_slice()),
            Box::from([unary!(2_usize), var!(0_u32)].as_slice()),
        )]
    };
    let run = |environment: Environment, [a, b]: [SourceRank; 2]| {
        let mut environment = booleans(environment);
        assert_eq!(
            admit_identity(&mut environment, a, plain),
            Ok(()),
            "`a` admits"
        );
        assert_eq!(
            admit_identity(&mut environment, b, plain),
            Ok(()),
            "`b` admits"
        );
        assert_eq!(
            admit_identity(&mut environment, rank(3_usize), law),
            Ok(()),
            "`c` admits"
        );
        environment
    };
    let in_order = run(Environment::recalling(trusting(), Arc::new(NoVerdicts)), [
        rank(1_usize),
        rank(2_usize),
    ]);
    assert!(
        matches!(
            in_order
                .entries()
                .get(3_usize)
                .map(crate::env::AdmittedDeclaration::key),
            Some(Maybe::Present(_))
        ),
        "`c` holds an entry key"
    );
    let Maybe::Present(receipt) = in_order.receipt(&signer)
    else {
        panic!("a run that checked keyed declarations gives a receipt");
    };
    let source: Arc<dyn VerdictSource> = Arc::new(Kept(vec![Arc::new(receipt)]));
    let admissions = |environment: &Environment| {
        environment
            .entries()
            .iter()
            .map(crate::env::AdmittedDeclaration::admission)
            .collect::<Vec<_>>()
    };
    let again = run(Environment::recalling(trusting(), Arc::clone(&source)), [
        rank(1_usize),
        rank(2_usize),
    ]);
    assert_eq!(
        admissions(&again),
        [Admission::Recalled; 4],
        "a run in order recalls each declaration, `c` among them"
    );
    let swapped = run(Environment::recalling(trusting(), source), [
        rank(2_usize),
        rank(1_usize),
    ]);
    assert_eq!(
        admissions(&swapped),
        [
            Admission::Recalled,
            Admission::Recalled,
            Admission::Recalled,
            Admission::Checked
        ],
        "the booleans, `a` and `b` are recalled, and `c` is checked"
    );
}
