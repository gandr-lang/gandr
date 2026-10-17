use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::FieldLabel;
use gandr_core_term::Summand;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::Convertibility;
use super::Deferral;
use super::Settlement;
use super::convert_computations;
use super::convert_values;
use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainValueId;
use crate::closure::Environment;
use crate::closure::ValueBody;
use crate::domain::BinderLevel;
use crate::domain::CompTermFace;
use crate::domain::Elimination;
use crate::domain::FlowFormer;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;

/// A domain literal over the non-negative integer `digits` spell, with
/// its payload minted in `core`.
///
/// # Specification
/// - requires: `digits` is a non-empty run of decimal digits.
/// - ensures: a reduced-face domain literal whose core payload is that integer.
/// - provides: the rigid leaves the step witnesses compare.
/// - panics: when `digits` is not decimal, which no fixture passes.
///
/// # Adequacy
/// - hypothesis: L2 — distinct decimal payloads separate through rigid guards,
///   while repeated equal payloads at distinct ids agree structurally;
///   replacing the requested integer or retaining a source face changes which
///   step answers.
/// - witness: `conv::tests::the_guard_answers_a_rigid_pair_identity_does_not`
/// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
#[spec(
        requires: !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ret| matches!(domain.value(ret), Some(crate::DomainValue::Literal { face: TermFace::Reduced, .. })),
    )]
fn literal(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    digits: String,
) -> DomainValueId
{
    let magnitude = Magnitude::from_decimal_text(digits).expect("the digits are decimal");
    let payload = Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude));
    let held = core.value_literal(payload.clone());
    domain.value_literal(held, &payload, TermFace::Reduced)
}

/// A closure over `return ⟨⟩` in the empty environment.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh closure id over a fresh core body.
/// - provides: the flexible part a thunk or a lambda fixture carries.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — independently suspended returners supply the two thunks
///   whose bodies require binder opening; reusing a body or adding a captured
///   binding changes the comparison path.
/// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
#[spec(ensures: |ret| domain.comp_closure(ret).is_some_and(|closure|
        [Zone::Intuitionistic, Zone::Linear].iter().all(|&zone|
            closure.environment().bindings(zone).is_empty())
        && matches!(closure.body(), crate::closure::CompBody::Source(body)
            if matches!(core.computation(body), Some(gandr_core_term::Computation::Return(value))
                if core.value(*value).and_then(gandr_core_term::Value::components).is_some_and(<[_]>::is_empty)))))]
fn closure(
    core: &mut CoreArena,
    domain: &mut DomainArena,
) -> CompClosureId
{
    let produced = core.value_unit();
    let body = core.computation_return(produced);
    domain.comp_closure_node(body, Environment::new())
}

/// A value-position neutral over `head` with `unfolding`.
///
/// # Specification
/// - requires: `unfolding` is rigid unless `head` is a declaration.
/// - ensures: a reduced-face value standing for a spineless neutral.
/// - provides: the stuck values the deferral witnesses compare.
/// - panics: when the arena refuses the neutral, which no fixture provokes.
///
/// # Adequacy
/// - hypothesis: L2 — rigid and defined value heads distinguish a separating
///   mismatch from unfolding deferral, while a rigid value against a thunk
///   waits for a binder; changing the head or face changes the settlement.
/// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
#[spec(ensures: |ret| match domain.value(ret) {
        Some(&crate::DomainValue::Neutral { neutral, face: TermFace::Reduced }) =>
            domain.neutral(neutral).is_some_and(|node| node.head() == head
                && node.unfolding() == unfolding && node.spine().is_empty()),
        _ => false,
    })]
fn stuck(
    domain: &mut DomainArena,
    head: NeutralHead,
    unfolding: Unfolding,
) -> DomainValueId
{
    let neutral = domain
        .neutral_node(head, Vec::new(), unfolding)
        .expect("the head may carry the face");
    domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("a spineless neutral stands in a value position")
}

/// A computation-position neutral over `head` with `spine` and
/// `unfolding`.
///
/// # Specification
/// - requires: `unfolding` is rigid unless `head` is a declaration.
/// - ensures: a reduced-face computation standing for that neutral.
/// - provides: the stuck computations the spine witnesses compare.
/// - panics: when the arena refuses the neutral, which no fixture provokes.
///
/// # Adequacy
/// - hypothesis: L2 — equal-shaped spines under rigid and loaded heads
///   distinguish refutation from unfolding deferral, and different head indices
///   and arities separate rigid families; changing the neutral represented
///   changes those results.
/// - witness: `conv::tests::a_mismatch_separates_only_beneath_a_rigid_head`
/// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
#[spec(ensures: |ret| match domain.computation(ret) {
        Some(&crate::DomainComp::Neutral { neutral, face: CompTermFace::Reduced }) =>
            domain.neutral(neutral).is_some_and(|node| node.head() == head && node.unfolding() == unfolding),
        _ => false,
    })]
fn stuck_comp(
    domain: &mut DomainArena,
    head: NeutralHead,
    spine: Vec<Elimination>,
    unfolding: Unfolding,
) -> DomainCompId
{
    let neutral = domain
        .neutral_node(head, spine, unfolding)
        .expect("the head may carry the face");
    domain.comp_neutral(neutral, CompTermFace::Reduced)
}

/// The innermost intuitionistic variable as a neutral head.
///
/// # Specification
/// trivial.
fn variable() -> NeutralHead
{
    NeutralHead::Variable {
        zone: Zone::Intuitionistic,
        level: BinderLevel::from(0_u32),
    }
}

#[test]
fn identity_answers_one_node_and_one_source_term()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(TermFace::Reduced);
    assert_eq!(
        Ok(Settlement::Identical),
        convert_values(&core, &domain, unit, unit),
        "one id is one value"
    );

    let produced = core.value_unit();
    let suspended = core.computation_return(produced);
    let source = core.value_thunk(suspended);
    let first = closure(&mut core, &mut domain);
    let second = closure(&mut core, &mut domain);
    let one = domain.value_thunk(first, TermFace::Source(source));
    let other = domain.value_thunk(second, TermFace::Source(source));
    assert_eq!(
        Ok(Settlement::Identical),
        convert_values(&core, &domain, one, other),
        "two thunks evaluated from one source term are one value, which no guard could \
             say: a thunk's word is flexible"
    );
}

#[test]
fn the_guard_answers_a_rigid_pair_identity_does_not()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(TermFace::Reduced);
    let one = literal(&mut core, &mut domain, String::from("1"));
    let two = literal(&mut core, &mut domain, String::from("2"));
    let left = domain.value_tuple([unit, one], TermFace::Reduced);
    let right = domain.value_tuple([unit, two], TermFace::Reduced);
    let settled = convert_values(&core, &domain, left, right);
    assert_eq!(
        Ok(Settlement::GuardedApart),
        settled,
        "two ids with reduced faces pass step 1, and two rigid words that differ settle \
             the pair at step 2"
    );
    assert_eq!(
        Ok(Convertibility::Distinct),
        settled.map(Settlement::verdict),
        "which is a distinct answer"
    );
}

#[test]
fn structure_answers_what_the_guard_cannot()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();

    let left_unit = domain.value_unit(TermFace::Reduced);
    let left_one = literal(&mut core, &mut domain, String::from("1"));
    let right_unit = domain.value_unit(TermFace::Reduced);
    let right_one = literal(&mut core, &mut domain, String::from("1"));
    let left = domain.value_tuple([left_unit, left_one], TermFace::Reduced);
    let right = domain.value_tuple([right_unit, right_one], TermFace::Reduced);
    assert_eq!(
        Ok(Settlement::StructurallyEqual),
        convert_values(&core, &domain, left, right),
        "equal content at distinct ids folds to one word, which step 2 may not read as \
             convertible; step 3 does"
    );

    let left_closure = closure(&mut core, &mut domain);
    let right_closure = closure(&mut core, &mut domain);
    let left_thunk = domain.value_thunk(left_closure, TermFace::Reduced);
    let right_thunk = domain.value_thunk(right_closure, TermFace::Reduced);
    let two = literal(&mut core, &mut domain, String::from("2"));
    let left = domain.value_tuple([left_thunk, left_unit], TermFace::Reduced);
    let right = domain.value_tuple([right_thunk, two], TermFace::Reduced);
    assert_eq!(
        Ok(Settlement::StructurallyApart),
        convert_values(&core, &domain, left, right),
        "a thunk makes both words flexible, so step 2 is silent, and step 3 finds the \
             unit against the literal"
    );
}

#[test]
fn a_pair_needing_an_unfolding_or_a_binder_is_deferred()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();

    let defined = stuck(
        &mut domain,
        NeutralHead::Constant(ConstantIndex::from(0_usize)),
        Unfolding::Unforced(GlobalIndex::from(3_u32)),
    );
    let axiom = stuck(
        &mut domain,
        NeutralHead::Constant(ConstantIndex::from(1_usize)),
        Unfolding::Rigid,
    );
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Unfolding)),
        convert_values(&core, &domain, defined, axiom),
        "two heads differ, but one has a body that may unfold into the other"
    );
    let unit = domain.value_unit(TermFace::Reduced);
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Unfolding)),
        convert_values(&core, &domain, defined, unit),
        "and a definition may unfold into a constructor"
    );

    let rigid = stuck(&mut domain, variable(), Unfolding::Rigid);
    let suspended = closure(&mut core, &mut domain);
    let thunk = domain.value_thunk(suspended, TermFace::Reduced);
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Binder)),
        convert_values(&core, &domain, thunk, rigid),
        "a thunk against a stuck variable waits for the η-rule that opens a binder"
    );

    let elsewhere = closure(&mut core, &mut domain);
    let other_thunk = domain.value_thunk(elsewhere, TermFace::Reduced);
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Binder)),
        convert_values(&core, &domain, thunk, other_thunk),
        "and two closures over different bodies compare only once their binders open"
    );

    let lambda = domain.comp_lambda(suspended, CompTermFace::Reduced);
    let applied = stuck_comp(
        &mut domain,
        variable(),
        Vec::from([Elimination::Force]),
        Unfolding::Rigid,
    );
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Binder)),
        convert_computations(&core, &domain, lambda, applied),
        "a lambda against a stuck computation waits for function η"
    );
}

#[test]
fn a_mismatch_separates_only_beneath_a_rigid_head()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let one = literal(&mut core, &mut domain, String::from("1"));
    let two = literal(&mut core, &mut domain, String::from("2"));
    let continuation = closure(&mut core, &mut domain);
    let spine = |argument| {
        Vec::from([
            Elimination::Force,
            Elimination::Apply(argument),
            Elimination::Bind(continuation),
        ])
    };

    let rigid_left = stuck_comp(&mut domain, variable(), spine(one), Unfolding::Rigid);
    let rigid_right = stuck_comp(&mut domain, variable(), spine(two), Unfolding::Rigid);
    assert_eq!(
        Ok(Settlement::StructurallyApart),
        convert_computations(&core, &domain, rigid_left, rigid_right),
        "a bind makes both words flexible; beneath a rigid head the differing arguments \
             separate the two stuck computations"
    );

    let defined = NeutralHead::Constant(ConstantIndex::from(0_usize));
    let body = Unfolding::Unforced(GlobalIndex::from(3_u32));
    let unfolding_left = stuck_comp(&mut domain, defined, spine(one), body);
    let unfolding_right = stuck_comp(&mut domain, defined, spine(two), body);
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Unfolding)),
        convert_computations(&core, &domain, unfolding_left, unfolding_right),
        "beneath a head with a body the same mismatch defers, because the unfolded body \
             may never read its argument"
    );
}

#[test]
fn computations_settle_by_their_weak_heads()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let suspended = closure(&mut core, &mut domain);
    let thunk = domain.value_thunk(suspended, TermFace::Reduced);
    let one = literal(&mut core, &mut domain, String::from("1"));
    let two = literal(&mut core, &mut domain, String::from("2"));
    let left_pair = domain.value_tuple([thunk, one], TermFace::Reduced);
    let right_pair = domain.value_tuple([thunk, two], TermFace::Reduced);
    let left = domain.comp_return(left_pair, CompTermFace::Reduced);
    let right = domain.comp_return(right_pair, CompTermFace::Reduced);
    assert_eq!(
        Ok(Settlement::StructurallyApart),
        convert_computations(&core, &domain, left, right),
        "two returners compare by the values they carry"
    );

    let lambda = domain.comp_lambda(suspended, CompTermFace::Reduced);
    assert_eq!(
        Ok(Settlement::StructurallyApart),
        convert_computations(&core, &domain, lambda, left),
        "a lambda and a returner are different weak heads"
    );

    let forced = stuck_comp(
        &mut domain,
        variable(),
        Vec::from([Elimination::Force]),
        Unfolding::Rigid,
    );
    assert_eq!(
        Ok(Settlement::StructurallyApart),
        convert_computations(&core, &domain, left, forced),
        "a returner against a rigid stuck computation separates"
    );
    let defined = stuck_comp(
        &mut domain,
        NeutralHead::Constant(ConstantIndex::from(0_usize)),
        Vec::from([Elimination::Force]),
        Unfolding::Unforced(GlobalIndex::from(3_u32)),
    );
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Unfolding)),
        convert_computations(&core, &domain, left, defined),
        "and against one whose head may unfold into a returner it defers"
    );
}

#[test]
fn a_shared_graph_is_compared_once_per_pair()
{
    let core = CoreArena::new();
    let mut domain = DomainArena::new();
    let mut left = domain.value_unit(TermFace::Reduced);
    let mut right = domain.value_unit(TermFace::Reduced);
    let mut remaining = 64_u32;
    while remaining > 0_u32 {
        left = domain.value_tuple([left, left], TermFace::Reduced);
        right = domain.value_tuple([right, right], TermFace::Reduced);
        remaining = remaining.saturating_sub(1_u32);
    }
    assert_eq!(
        Ok(Settlement::StructurallyEqual),
        convert_values(&core, &domain, left, right),
        "each graph expands to 2⁶⁴ leaves, and the walk meets 65 distinct pairs"
    );
}

#[test]
fn family_spines_are_separated_by_head_index_and_arity()
{
    /// The rigid family at `family` applied statically to `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn applied(
        domain: &mut DomainArena,
        family: ConstantIndex,
        arguments: &[DomainValueId],
    ) -> DomainValueId
    {
        let spine = arguments
            .iter()
            .map(|&argument| Elimination::StaticApply(argument))
            .collect();
        let neutral = domain
            .neutral_node(NeutralHead::Constant(family), spine, Unfolding::Rigid)
            .expect("a rigid family mints");
        domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a static spine stands as a value")
    }

    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let one = literal(&mut core, &mut domain, String::from("1"));
    let two = literal(&mut core, &mut domain, String::from("2"));
    let f_one = applied(&mut domain, ConstantIndex::from(0_usize), &[one]);
    let f_one_again = applied(&mut domain, ConstantIndex::from(0_usize), &[one]);
    let g_one = applied(&mut domain, ConstantIndex::from(1_usize), &[one]);
    let f_one_two = applied(&mut domain, ConstantIndex::from(0_usize), &[one, two]);
    let f_two = applied(&mut domain, ConstantIndex::from(0_usize), &[two]);
    assert_eq!(
        Ok(Settlement::StructurallyEqual),
        convert_values(&core, &domain, f_one, f_one_again),
        "one head at one arity over one argument is one family instance"
    );
    assert_eq!(
        Ok(Settlement::GuardedApart),
        convert_values(&core, &domain, f_one, g_one),
        "two head indices fold to two words"
    );
    assert_eq!(
        Ok(Settlement::GuardedApart),
        convert_values(&core, &domain, f_one, f_one_two),
        "two arities over one head fold to two words"
    );
    assert_eq!(
        Ok(Settlement::GuardedApart),
        convert_values(&core, &domain, f_one, f_two),
        "and two arguments at one head and arity fold apart too"
    );
}

#[test]
fn identical_truncated_values_are_refused()
{
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let value = domain.value_unit(TermFace::Reduced);
    assert_eq!(
        Ok(super::Early::Identical),
        super::early_values(&domain, value, value)
    );
    domain.truncate_to(floor);
    assert!(domain.value(value).is_none());
    assert_eq!(
        Err(super::ConversionFault::Domain(crate::DomainFault::Dangling)),
        super::early_values(&domain, value, value)
    );
}

#[test]
fn identical_truncated_computations_are_refused()
{
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let value = domain.value_unit(TermFace::Reduced);
    let computation = domain.comp_return(value, CompTermFace::Reduced);
    assert_eq!(
        Ok(super::Early::Identical),
        super::early_comps(&domain, computation, computation)
    );
    domain.truncate_to(floor);
    assert!(domain.computation(computation).is_none());
    assert_eq!(
        Err(super::ConversionFault::Domain(crate::DomainFault::Dangling)),
        super::early_comps(&domain, computation, computation)
    );
}

#[test]
fn identical_truncated_neutrals_and_closures_are_refused()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let suspended = closure(&mut core, &mut domain);
    let neutral = domain
        .neutral_node(variable(), Vec::new(), Unfolding::Rigid)
        .expect("a variable is rigid");
    {
        let mut walk = super::Walk::new(&core, &domain);
        assert_eq!(
            Ok(super::Local::Agree),
            walk.neutrals(neutral, neutral, super::Context::Rigid)
        );
        assert_eq!(Ok(super::Local::Agree), walk.closures(suspended, suspended));
    }
    domain.truncate_to(floor);
    let mut walk = super::Walk::new(&core, &domain);
    let neutral_result = walk.neutrals(neutral, neutral, super::Context::Rigid);
    let closure_result = walk.closures(suspended, suspended);
    let refused = Err(super::ConversionFault::Domain(crate::DomainFault::Dangling));
    assert_eq!((refused, refused), (neutral_result, closure_result));
}

#[test]
fn the_first_deferral_is_retained_until_a_rigid_refutation()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let first = closure(&mut core, &mut domain);
    let second = closure(&mut core, &mut domain);
    let first_thunk = domain.value_thunk(first, TermFace::Reduced);
    let second_thunk = domain.value_thunk(second, TermFace::Reduced);
    let defined = stuck(
        &mut domain,
        NeutralHead::Constant(ConstantIndex::from(0_usize)),
        Unfolding::Unforced(GlobalIndex::from(0_u32)),
    );
    let unit = domain.value_unit(TermFace::Reduced);
    for (left_first, left_second, right_first, right_second, reason) in [
        (first_thunk, defined, second_thunk, unit, Deferral::Binder),
        (
            defined,
            first_thunk,
            unit,
            second_thunk,
            Deferral::Unfolding,
        ),
    ] {
        let left = domain.value_tuple([left_first, left_second], TermFace::Reduced);
        let right = domain.value_tuple([right_first, right_second], TermFace::Reduced);
        let answer = convert_values(&core, &domain, left, right).expect("the pair is well formed");
        assert_eq!(Settlement::Deferred(reason), answer);
        assert_eq!(Convertibility::Undecided, answer.verdict());
        assert_eq!(
            Convertibility::Convertible,
            convert_values(&core, &domain, left, left)
                .expect("live identity agrees")
                .verdict()
        );
        let one = literal(&mut core, &mut domain, String::from("1"));
        let left = domain.value_tuple([left, unit], TermFace::Reduced);
        let right = domain.value_tuple([right, one], TermFace::Reduced);
        let answer = convert_values(&core, &domain, left, right).expect("the mismatch resolves");
        assert_eq!(Settlement::StructurallyApart, answer);
        assert_eq!(Convertibility::Distinct, answer.verdict());
    }
}

#[test]
fn a_payload_read_refuses_nonliteral_and_missing_nodes()
{
    let mut core = CoreArena::new();
    let floor = core.watermark();
    let nonliteral = core.value_unit();
    let domain = DomainArena::new();
    assert_eq!(
        Err(super::ConversionFault::LiteralPayload {
            literal: nonliteral
        }),
        super::Walk::new(&core, &domain).payload(nonliteral)
    );
    core.truncate_to(floor);
    assert_eq!(
        Err(super::ConversionFault::LiteralPayload {
            literal: nonliteral
        }),
        super::Walk::new(&core, &domain).payload(nonliteral)
    );
}

/// A thunk both sides of a fixture share: one id agrees with itself, and its
/// flexible guard leaves any value holding it to the structural walk.
///
/// # Specification
/// trivial.
fn shared_thunk(
    core: &mut CoreArena,
    domain: &mut DomainArena,
) -> DomainValueId
{
    let suspended = closure(core, domain);
    domain.value_thunk(suspended, TermFace::Reduced)
}

#[test]
fn each_former_agrees_with_its_twin_at_another_id()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let thunk = shared_thunk(&mut core, &mut domain);
    let unit = domain.value_unit(TermFace::Reduced);

    let unit_type = core.value_type_unit();
    let datatype = domain.value_closure_node(ValueBody::ValueType(unit_type), Environment::new());
    let constructor = |domain: &mut DomainArena, tag: usize| {
        let fields = domain.hold_fields([thunk]);
        domain.value_constructor(
            datatype,
            ConstructorTag::from(tag),
            fields,
            TermFace::Reduced,
        )
    };
    let label = FieldLabel::from(String::from("x"));
    let unit_term = core.value_unit();
    let labelled = core.value_record(BTreeMap::from([(label, unit_term)]));
    let record = |domain: &mut DomainArena| {
        let fields = domain.hold_fields([unit]);
        domain
            .value_record(labelled, fields, TermFace::Reduced)
            .expect("the fields are live")
    };
    let lift = |domain: &mut DomainArena| {
        let target = domain.hold_level(Level::zero());
        domain.value_lift(target, thunk, TermFace::Reduced)
    };
    let pairs = [
        (
            "a constructor",
            constructor(&mut domain, 0),
            constructor(&mut domain, 0),
        ),
        ("a record", record(&mut domain), record(&mut domain)),
        (
            "a flow",
            domain.value_flow(FlowFormer::Then, [thunk, thunk], TermFace::Reduced),
            domain.value_flow(FlowFormer::Then, [thunk, thunk], TermFace::Reduced),
        ),
        (
            "an injection",
            domain.value_injection(Summand::from(1_usize), thunk, TermFace::Reduced),
            domain.value_injection(Summand::from(1_usize), thunk, TermFace::Reduced),
        ),
        ("a lift", lift(&mut domain), lift(&mut domain)),
    ];
    for (former, left, right) in pairs {
        assert_eq!(
            Ok(Settlement::StructurallyEqual),
            convert_values(&core, &domain, left, right),
            "{former} agrees with one of its own tag, labels, former, summand or level over \
             the same parts"
        );
    }
}

#[test]
fn two_flows_of_different_formers_are_apart_over_the_same_parts()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let thunk = shared_thunk(&mut core, &mut domain);
    let then = domain.value_flow(FlowFormer::Then, [thunk, thunk], TermFace::Reduced);
    let product = domain.value_flow(FlowFormer::Product, [thunk, thunk], TermFace::Reduced);
    assert_eq!(
        Ok(Settlement::StructurallyApart),
        convert_values(&core, &domain, then, product)
    );
}

#[test]
fn a_record_with_more_labels_than_fields_is_refused_on_either_side()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(TermFace::Reduced);
    let unit_term = core.value_unit();
    let narrow = core.value_record(BTreeMap::from([(
        FieldLabel::from(String::from("x")),
        unit_term,
    )]));
    let wide = core.value_record(BTreeMap::from([
        (FieldLabel::from(String::from("x")), unit_term),
        (FieldLabel::from(String::from("y")), unit_term),
    ]));
    let fields = domain.hold_fields([unit]);
    let formed = domain
        .value_record(narrow, fields, TermFace::Reduced)
        .expect("the fields are live");
    let fields = domain.hold_fields([unit]);
    let malformed = domain
        .value_record(wide, fields, TermFace::Reduced)
        .expect("the fields are live");
    for (left, right) in [(malformed, formed), (formed, malformed)] {
        assert_eq!(
            Err(super::ConversionFault::MachineInvariant),
            convert_values(&core, &domain, left, right)
        );
    }
}

#[test]
fn a_neutral_one_bind_short_of_its_twin_waits_for_return_eta()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let continuation = closure(&mut core, &mut domain);
    let bound = stuck_comp(
        &mut domain,
        variable(),
        Vec::from([Elimination::Force, Elimination::Bind(continuation)]),
        Unfolding::Rigid,
    );
    let forced = stuck_comp(
        &mut domain,
        variable(),
        Vec::from([Elimination::Force]),
        Unfolding::Rigid,
    );
    assert_eq!(
        Ok(Settlement::Deferred(Deferral::Binder)),
        convert_computations(&core, &domain, bound, forced)
    );
}

#[test]
fn two_cases_over_as_many_branches_compare_their_branches()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let branch = closure(&mut core, &mut domain);
    let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unit_type = core.value_type_unit();
    let motive = core.comp_type_returner(unit_type);
    let produced = core.value_unit();
    let returned = core.computation_return(produced);
    let data_case = core.computation_data_case(scrutinee, motive, Vec::from([returned]));
    let data_case = domain.comp_closure_node(data_case, Environment::new());
    let case = Elimination::Case(domain.hold_branches([branch, branch]));
    let other_case = Elimination::Case(domain.hold_branches([branch, branch]));
    let (data, other_data) = (
        Elimination::DataCase(data_case),
        Elimination::DataCase(data_case),
    );
    for (former, left, right) in [("case", case, other_case), ("data case", data, other_data)] {
        let left = stuck_comp(&mut domain, variable(), Vec::from([left]), Unfolding::Rigid);
        let right = stuck_comp(
            &mut domain,
            variable(),
            Vec::from([right]),
            Unfolding::Rigid,
        );
        assert_eq!(
            Ok(Settlement::StructurallyEqual),
            convert_computations(&core, &domain, left, right),
            "two {former} spines of one branch count over one branch agree"
        );
    }
}

#[test]
fn two_path_products_agree_component_by_component()
{
    let mut domain = DomainArena::new();
    let core = CoreArena::new();
    let path = stuck(&mut domain, variable(), Unfolding::Rigid);
    let left = domain.value_path_product(path, path, TermFace::Reduced);
    let right = domain.value_path_product(path, path, TermFace::Reduced);
    assert_eq!(
        Ok(gandr_core_term::CertificateEquality::Equal),
        super::equal_paths(&core, &domain, left, right)
    );
}

#[test]
fn a_neutral_path_agrees_only_at_its_own_head_with_no_spine()
{
    let mut core = CoreArena::new();
    let mut domain = DomainArena::new();
    let one = literal(&mut core, &mut domain, String::from("1"));
    let other_head = NeutralHead::Variable {
        zone: Zone::Intuitionistic,
        level: BinderLevel::from(1_u32),
    };
    let path = stuck(&mut domain, variable(), Unfolding::Rigid);
    let again = stuck(&mut domain, variable(), Unfolding::Rigid);
    let elsewhere = stuck(&mut domain, other_head, Unfolding::Rigid);
    let applied = domain
        .neutral_node(
            variable(),
            Vec::from([Elimination::StaticApply(one)]),
            Unfolding::Rigid,
        )
        .expect("a variable is rigid");
    let applied = domain
        .value_neutral(applied, TermFace::Reduced)
        .expect("a static spine stands as a value");
    let equal = Ok(gandr_core_term::CertificateEquality::Equal);
    let different = Ok(gandr_core_term::CertificateEquality::Different);
    for (left, right, expected, reading) in [
        (path, again, equal, "one head and no spine"),
        (path, elsewhere, different, "two heads"),
        (applied, again, different, "a spine on the left"),
        (again, applied, different, "a spine on the right"),
    ] {
        assert_eq!(
            expected,
            super::equal_paths(&core, &domain, left, right),
            "{reading}"
        );
    }
}
