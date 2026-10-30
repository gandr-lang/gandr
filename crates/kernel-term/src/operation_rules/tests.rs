use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use super::OperationNode;
use super::OperationRule;
use super::OperationRuleFault;
use super::OperationRuleRefusal;
use super::OperationRules;
use super::Overlapped;
use super::RuleScope;
use crate::presented::FieldCount;
use crate::presented::Presentation;
use crate::presented::PresentedRule;
use crate::presented::RewriteFuel;
use crate::presented::RuleIndex;
use crate::presented::RuleNode;
use crate::presented::RuleVariable;
use crate::term::ConstantIndex;
use crate::term::ConstructorTag;

/// The operation at position `$constant` applied to `$arity` subterms.
macro_rules! op {
    ($constant:expr, $arity:expr) => {
        OperationNode::Operation {
            constant: ConstantIndex::from($constant),
            arity: FieldCount::from($arity),
        }
    };
}

/// The test family's constructor `$tag`.
macro_rules! ctor {
    ($tag:expr) => {
        OperationNode::Constructor {
            family: ConstantIndex::from(FAMILY),
            tag: ConstructorTag::from($tag),
        }
    };
}

/// Pattern variable `$ordinal`.
macro_rules! var {
    ($ordinal:expr) => {
        OperationNode::Variable(RuleVariable::from($ordinal))
    };
}

/// A scope holding one free family whose constructors carry the given field
/// counts.
macro_rules! free {
    ($($fields:expr),* $(,)?) => {
        Scope {
            families: vec![(ConstantIndex::from(FAMILY), vec![$($fields),*], Presentation::default())],
            operations: Vec::new(),
        }
    };
}

/// Decide `$rules` as the definition at position `$own` over `$scope`.
macro_rules! decide {
    ($rules:expr, $own:expr, $scope:expr) => {
        OperationRules::new($rules).converge(
            ConstantIndex::from($own),
            $scope,
            &mut RewriteFuel::from(10_000_u64),
        )
    };
}

/// The declarations below a ruled definition: data declarations with their
/// field counts and presentations, and ruled definitions.
#[derive(Default)]
struct Scope
{
    /// Each family's position, field count per constructor and presentation.
    families: Vec<(ConstantIndex, Vec<usize>, Presentation)>,
    /// Each ruled definition's position and rules.
    operations: Vec<(ConstantIndex, OperationRules)>,
}

impl RuleScope for Scope
{
    /// The field count of `family`'s constructor `tag`.
    ///
    /// # Specification
    /// trivial.
    fn fields(
        &self,
        family: ConstantIndex,
        tag: ConstructorTag,
    ) -> Option<FieldCount>
    {
        let &(_, ref fields, _) = self.families.iter().find(|entry| entry.0 == family)?;
        fields.get(usize::from(tag)).copied().map(FieldCount::from)
    }

    /// `family`'s presentation.
    ///
    /// # Specification
    /// trivial.
    fn presentation(
        &self,
        family: ConstantIndex,
    ) -> Option<&Presentation>
    {
        self.families
            .iter()
            .find(|entry| entry.0 == family)
            .map(|entry| &entry.2)
    }

    /// The rules of the definition at `constant`.
    ///
    /// # Specification
    /// trivial.
    fn rules(
        &self,
        constant: ConstantIndex,
    ) -> Option<&OperationRules>
    {
        self.operations
            .iter()
            .find(|entry| entry.0 == constant)
            .map(|entry| &entry.1)
    }
}

/// The family every test builds over, at position 0.
const FAMILY: usize = 0;

/// The rule `left ==> right`.
///
/// # Specification
/// trivial.
fn rule(
    left: &[OperationNode],
    right: &[OperationNode],
) -> OperationRule
{
    OperationRule::new(Box::from(left), Box::from(right))
}

/// Booleans: `False`, `True`.
const FALSE: usize = 0;
/// Booleans: `False`, `True`.
const TRUE: usize = 1;

#[test]
fn two_overlapping_rules_that_join_converge()
{
    let scope = free!(0, 0);
    let or = |left: &[OperationNode], right: OperationNode| {
        let mut call = vec![op!(1_usize, 2_usize)];
        call.extend_from_slice(left);
        rule(&call, &[right])
    };
    // `or(True, y)` and `or(x, True)` overlap at `or(True, True)`, where both
    // give `True`.
    let rules = vec![
        or(&[ctor!(TRUE), var!(0_u32)], ctor!(TRUE)),
        or(&[var!(0_u32), ctor!(TRUE)], ctor!(TRUE)),
        or(&[ctor!(FALSE), ctor!(FALSE)], ctor!(FALSE)),
    ];
    assert_eq!(
        decide!(rules, 1_usize, &scope),
        Ok(()),
        "the overlap joins at True"
    );
}

#[test]
fn two_overlapping_rules_that_part_are_refused_at_the_later()
{
    let scope = free!(0, 0);
    let rules = vec![
        rule(&[op!(1_usize, 2_usize), ctor!(TRUE), var!(0_u32)], &[
            ctor!(TRUE),
        ]),
        rule(&[op!(1_usize, 2_usize), var!(0_u32), ctor!(TRUE)], &[
            ctor!(FALSE),
        ]),
    ];
    assert_eq!(
        decide!(rules, 1_usize, &scope),
        Err(OperationRuleRefusal {
            rule: RuleIndex::from(1_usize),
            fault: OperationRuleFault::Diverges(Overlapped::Operation(RuleIndex::from(0_usize))),
        }),
        "`or(True, True)` rewrites to True by the first rule and False by the second"
    );
}

/// Naturals: `Zero`, `Succ`.
const ZERO: usize = 0;
/// Naturals: `Zero`, `Succ`.
const SUCC: usize = 1;

#[test]
fn a_growing_rule_is_unoriented()
{
    let scope = free!(0, 1);
    let growing = vec![rule(&[op!(1_usize, 1_usize), var!(0_u32)], &[
        op!(1_usize, 1_usize),
        ctor!(SUCC),
        var!(0_u32),
    ])];
    assert_eq!(
        decide!(growing, 1_usize, &scope),
        Err(OperationRuleRefusal {
            rule: RuleIndex::from(0_usize),
            fault: OperationRuleFault::Unoriented,
        }),
        "`f(x) ==> f(Succ(x))` rebuilds its own call on a larger argument"
    );
    let descending = vec![
        rule(&[op!(1_usize, 1_usize), ctor!(ZERO)], &[ctor!(ZERO)]),
        rule(&[op!(1_usize, 1_usize), ctor!(SUCC), var!(0_u32)], &[
            op!(1_usize, 1_usize),
            var!(0_u32),
        ]),
    ];
    assert_eq!(
        decide!(descending, 1_usize, &scope),
        Ok(()),
        "recursion on a field descends"
    );
}

/// `add` over naturals at position 1.
///
/// # Specification
/// trivial.
fn add() -> OperationRules
{
    OperationRules::new(vec![
        rule(&[op!(1_usize, 2_usize), ctor!(ZERO), var!(0_u32)], &[var!(
            0_u32
        )]),
        rule(
            &[op!(1_usize, 2_usize), ctor!(SUCC), var!(0_u32), var!(1_u32)],
            &[ctor!(SUCC), op!(1_usize, 2_usize), var!(0_u32), var!(1_u32)],
        ),
    ])
}

#[test]
fn an_operation_over_an_earlier_one_converges()
{
    let mut scope = free!(0, 1);
    assert_eq!(
        add().converge(
            ConstantIndex::from(1_usize),
            &scope,
            &mut RewriteFuel::from(100_u64)
        ),
        Ok(()),
        "add's rules are orthogonal and descend"
    );
    scope.operations.push((ConstantIndex::from(1_usize), add()));
    // `double(Zero)` and `double(x)` overlap at `double(Zero)`: `Zero` against
    // `add(Zero, Zero)`, which add's own rules bring to `Zero`.
    let double = vec![
        rule(&[op!(2_usize, 1_usize), ctor!(ZERO)], &[ctor!(ZERO)]),
        rule(&[op!(2_usize, 1_usize), var!(0_u32)], &[
            op!(1_usize, 2_usize),
            var!(0_u32),
            var!(0_u32),
        ]),
    ];
    assert_eq!(
        decide!(double.clone(), 2_usize, &scope),
        Ok(()),
        "the pair joins through add"
    );
    // The same rules one position lower call add from below: add is not
    // admitted before them, so the call names no known operation.
    let lowered = vec![rule(&[op!(1_usize, 1_usize), var!(0_u32)], &[
        op!(2_usize, 2_usize),
        var!(0_u32),
        var!(0_u32),
    ])];
    assert_eq!(
        decide!(lowered, 1_usize, &scope).map_err(|refusal| refusal.fault),
        Err(OperationRuleFault::UnknownOperation),
        "an operation calls only operations admitted before it"
    );
    // An add that only reads a successor leaves `add(Zero, Zero)` stuck, apart
    // from `Zero`: the callee's rules are read, never assumed.
    scope.operations.clear();
    scope.operations.push((
        ConstantIndex::from(1_usize),
        OperationRules::new(vec![rule(
            &[op!(1_usize, 2_usize), ctor!(SUCC), var!(0_u32), var!(1_u32)],
            &[var!(1_u32)],
        )]),
    ));
    assert_eq!(
        decide!(double, 2_usize, &scope),
        Err(OperationRuleRefusal {
            rule: RuleIndex::from(1_usize),
            fault: OperationRuleFault::Diverges(Overlapped::Operation(RuleIndex::from(0_usize))),
        }),
        "`add(Zero, Zero)` is stuck under an add with no rule for Zero"
    );
}

/// Integers presented: `Zero`, `Succ`, `Pred`, with `Succ(Pred(x)) ==> x`
/// and `Pred(Succ(x)) ==> x`.
///
/// # Specification
/// trivial.
fn integers() -> Scope
{
    let side = |nodes: &[RuleNode]| Box::from(nodes);
    let constructor = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
    let variable = RuleNode::Variable(RuleVariable::from(0_u32));
    let presentation = Presentation::new(vec![
        PresentedRule::new(
            side(&[constructor(1), constructor(2), variable]),
            side(&[variable]),
        ),
        PresentedRule::new(
            side(&[constructor(2), constructor(1), variable]),
            side(&[variable]),
        ),
    ]);
    Scope {
        families: vec![(ConstantIndex::from(FAMILY), vec![0, 1, 1], presentation)],
        operations: Vec::new(),
    }
}

#[test]
fn a_pattern_below_a_presented_rule_is_decided_against_it()
{
    let scope = integers();
    // The identity homomorphism: its pattern `Succ(x)` meets `Succ(Pred(y))`,
    // and both reducts reach `h(y)`.
    let homomorphism = vec![
        rule(&[op!(1_usize, 1_usize), ctor!(0_usize)], &[ctor!(0_usize)]),
        rule(&[op!(1_usize, 1_usize), ctor!(1_usize), var!(0_u32)], &[
            ctor!(1_usize),
            op!(1_usize, 1_usize),
            var!(0_u32),
        ]),
        rule(&[op!(1_usize, 1_usize), ctor!(2_usize), var!(0_u32)], &[
            ctor!(2_usize),
            op!(1_usize, 1_usize),
            var!(0_u32),
        ]),
    ];
    assert_eq!(
        decide!(homomorphism, 1_usize, &scope),
        Ok(()),
        "a homomorphism respects the rules"
    );
    // Reading `Succ(x)` as "x is a predecessor" tells `Succ(Pred(y))` apart
    // from `y`.
    let projection = vec![
        rule(&[op!(1_usize, 1_usize), ctor!(0_usize)], &[ctor!(0_usize)]),
        rule(&[op!(1_usize, 1_usize), ctor!(1_usize), var!(0_u32)], &[
            var!(0_u32),
        ]),
        rule(&[op!(1_usize, 1_usize), ctor!(2_usize), var!(0_u32)], &[
            ctor!(2_usize),
            ctor!(2_usize),
            var!(0_u32),
        ]),
    ];
    assert_eq!(
        decide!(projection, 1_usize, &scope),
        Err(OperationRuleRefusal {
            rule: RuleIndex::from(1_usize),
            fault: OperationRuleFault::Diverges(Overlapped::Presented {
                family: ConstantIndex::from(FAMILY),
                rule: RuleIndex::from(0_usize),
            }),
        }),
        "`p(Succ(Pred(y)))` is `Pred(y)` by p's rule and `p(y)` by the presentation"
    );
}

#[test]
fn a_malformed_rule_is_refused_by_its_fault()
{
    let mut scope = free!(0, 1);
    scope.operations.push((ConstantIndex::from(1_usize), add()));
    let results = OperationNode::Results(FieldCount::from(0_usize));
    let cases: [(OperationRule, OperationRuleFault); 9] = [
        (
            rule(&[op!(1_usize, 1_usize), var!(0_u32)], &[var!(0_u32)]),
            OperationRuleFault::Head,
        ),
        (
            rule(&[op!(2_usize, 1_usize), results], &[ctor!(ZERO)]),
            OperationRuleFault::NotAPattern,
        ),
        (
            rule(
                &[op!(2_usize, 1_usize), op!(3_usize, 1_usize), var!(0_u32)],
                &[var!(0_u32)],
            ),
            OperationRuleFault::UnknownOperation,
        ),
        (
            rule(&[op!(2_usize, 1_usize), var!(0_u32)], &[
                op!(1_usize, 2_usize),
                results,
                var!(0_u32),
            ]),
            OperationRuleFault::Results,
        ),
        (
            rule(&[op!(2_usize, 1_usize), ctor!(5_usize)], &[ctor!(ZERO)]),
            OperationRuleFault::UnknownConstructor,
        ),
        (
            rule(&[op!(2_usize, 1_usize), var!(0_u32)], &[
                op!(3_usize, 1_usize),
                var!(0_u32),
            ]),
            OperationRuleFault::UnknownOperation,
        ),
        (
            rule(&[op!(2_usize, 1_usize), var!(0_u32), var!(1_u32)], &[var!(
                0_u32
            )]),
            OperationRuleFault::Arity,
        ),
        (
            rule(&[op!(2_usize, 1_usize), ctor!(SUCC), var!(1_u32)], &[
                ctor!(ZERO),
            ]),
            OperationRuleFault::NonLinear,
        ),
        (
            rule(&[op!(2_usize, 1_usize), var!(0_u32)], &[var!(1_u32)]),
            OperationRuleFault::Unbound,
        ),
    ];
    for (malformed, fault) in cases {
        let first = rule(&[op!(2_usize, 1_usize), ctor!(ZERO)], &[ctor!(ZERO)]);
        assert_eq!(
            decide!(vec![first, malformed], 2_usize, &scope),
            Err(OperationRuleRefusal {
                rule: RuleIndex::from(1_usize),
                fault,
            }),
            "each malformation is named at its rule"
        );
    }
}

/// `add`'s rules at position 1 with `law` after them.
///
/// # Specification
/// trivial.
fn add_with(law: OperationRule) -> Vec<OperationRule>
{
    let mut rules = add().rules().to_vec();
    rules.push(law);
    rules
}

/// `add(add(m, n), k)`, the left side of every law over add's own call.
///
/// # Specification
/// trivial.
fn nested() -> [OperationNode; 5]
{
    [
        op!(1_usize, 2_usize),
        op!(1_usize, 2_usize),
        var!(0_u32),
        var!(1_u32),
        var!(2_u32),
    ]
}

#[test]
fn a_law_over_its_own_call_converges_1510()
{
    let scope = free!(0, 1);
    // `add(add(m, n), k) ==> add(m, add(n, k))` overlaps add's two rules at
    // its inner call and itself there; each pair joins through the law.
    let associative = rule(&nested(), &[
        op!(1_usize, 2_usize),
        var!(0_u32),
        op!(1_usize, 2_usize),
        var!(1_u32),
        var!(2_u32),
    ]);
    assert_eq!(
        decide!(add_with(associative), 1_usize, &scope),
        Ok(()),
        "associativity converges with add's rules"
    );
}

#[test]
fn a_law_parting_at_its_call_is_refused_1510()
{
    let scope = free!(0, 1);
    // `add(add(Zero, n), k)` is `k` by the law and `add(n, k)` by add's first
    // rule at the inner call.
    let parting = rule(&nested(), &[var!(2_u32)]);
    assert_eq!(
        decide!(add_with(parting), 1_usize, &scope),
        Err(OperationRuleRefusal {
            rule: RuleIndex::from(2_usize),
            fault: OperationRuleFault::Diverges(Overlapped::Operation(RuleIndex::from(0_usize))),
        }),
        "the law parts from add's first rule at its call"
    );
}

#[test]
fn a_law_over_an_earlier_call_is_decided_against_its_rules_1510()
{
    let mut scope = free!(0, 1);
    scope.operations.push((ConstantIndex::from(1_usize), add()));
    // `double` at position 2, with a law over add's call.
    let double = |law: &[OperationNode]| {
        vec![
            rule(&[op!(2_usize, 1_usize), ctor!(ZERO)], &[ctor!(ZERO)]),
            rule(&[op!(2_usize, 1_usize), ctor!(SUCC), var!(0_u32)], &[
                ctor!(SUCC),
                ctor!(SUCC),
                op!(2_usize, 1_usize),
                var!(0_u32),
            ]),
            rule(
                &[
                    op!(2_usize, 1_usize),
                    op!(1_usize, 2_usize),
                    var!(0_u32),
                    var!(1_u32),
                ],
                law,
            ),
        ]
    };
    let distributes = [
        op!(1_usize, 2_usize),
        op!(2_usize, 1_usize),
        var!(0_u32),
        op!(2_usize, 1_usize),
        var!(1_u32),
    ];
    assert_eq!(
        decide!(double(&distributes), 2_usize, &scope),
        Ok(()),
        "`double(add(m, n)) ==> add(double(m), double(n))` joins with add's rules"
    );
    let forgets = [op!(2_usize, 1_usize), var!(0_u32)];
    assert_eq!(
        decide!(double(&forgets), 2_usize, &scope),
        Err(OperationRuleRefusal {
            rule: RuleIndex::from(2_usize),
            fault: OperationRuleFault::Diverges(Overlapped::Called {
                constant: ConstantIndex::from(1_usize),
                rule: RuleIndex::from(0_usize),
            }),
        }),
        "`double(add(Zero, n))` is `Zero` by the law and `double(n)` by add's rule"
    );
}
