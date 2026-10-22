use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Classifier;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::SortParameter;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::shift_value_type;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use proptest::collection::vec;
use proptest::prelude::ProptestConfig;
use proptest::prelude::prop_assert_eq;
use proptest::prelude::proptest;

use super::classify_comp_type;
use super::classify_value_type;
use super::form_comp_type;
use super::form_value_type;
use super::path_code;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::fixture::dangling_value_type;
use crate::fixture::seed;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;

/// The level `n`.
///
/// # Specification
/// trivial.
fn level(n: LevelConstant) -> Level
{
    Level::constant(n)
}

/// The classifier of a value type at level `n`.
///
/// # Specification
/// trivial.
fn value_at(n: LevelConstant) -> Classifier
{
    Classifier {
        sort: GroundSort::Value,
        level: level(n),
    }
}

/// The classifier of a computation type at level `n`.
///
/// # Specification
/// trivial.
fn comp_at(n: LevelConstant) -> Classifier
{
    Classifier {
        sort: GroundSort::Computation,
        level: level(n),
    }
}

/// Form `value_type` in `context` and classify it.
///
/// # Specification
/// - requires: nothing; invalid types are refused by formation.
/// - ensures: success supplies the value-sort classifier of the type.
/// - fails: formation or classification refuses the type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 over the bounded generated type programs, with L3 former
///   and dangling-id cases, compares the complete classifier or named refusal;
///   this separates wrong sorts, levels and lost failures.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::unsupported_forms_have_nominal_kinds`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|classifier| classifier.sort == GroundSort::Value) == ret.is_ok())]
fn classified(
    context: &mut CheckingContext<'_>,
    value_type: ValueTypeId,
) -> Result<Classifier, CheckRefusal>
{
    let formed = form_value_type(context, value_type)?;
    classify_value_type(context, formed)
}

/// Form `comp_type` in `context` and classify it.
///
/// # Specification
/// - requires: nothing; invalid types are refused by formation.
/// - ensures: success supplies the computation-sort classifier.
/// - fails: formation or classification refuses the type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — returners, arrows and dependent arrows expose exact sorts
///   and joined levels, separating swapped families and a dropped premise
///   level; arbitrary generated computation trees are not claimed.
/// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::the_dependent_arrow_forms_at_the_join_of_its_levels`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|classifier| classifier.sort == GroundSort::Computation) == ret.is_ok())]
fn classified_comp(
    context: &mut CheckingContext<'_>,
    comp_type: CompTypeId,
) -> Result<Classifier, CheckRefusal>
{
    let formed = form_comp_type(context, comp_type)?;
    classify_comp_type(context, formed)
}

#[test]
fn universe_families_form_one_level_up_in_the_value_sort()
{
    let mut arena = CoreArena::new();
    let value = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let computation =
        arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    assert_ne!(
        value, computation,
        "the two families are two nodes at one level"
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let one = LevelConstant::from(1_u64);
    assert_eq!(classified(&mut context, value), Ok(value_at(one)));
    assert_eq!(
        classified(&mut context, computation),
        Ok(value_at(one)),
        "the computation universe is itself a value type, one level up"
    );
}

/// Every supported classifier is formed at its semantic level, and
/// unsupported classifiers are refused by their boundary.
#[test]
fn every_value_type_constructor_has_a_formation_rule()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_constant(ConstantIndex::from(0_usize));
    let closed = arena.value_quote(unit);
    let path = arena.value_type_path_universe(closed, closed);
    let point = arena.value_unit();
    let element_path = arena.value_type_path(unit, point, point);
    let one = LevelConstant::from(1_u64);
    let zero = LevelConstant::from(0_u64);
    let rows: [(ValueTypeId, Result<Classifier, UnadmittedFormer>); 14] = [
        (path, Ok(value_at(zero))),
        (element_path, Ok(value_at(zero))),
        (
            arena.value_type_path(small, closed, closed),
            Ok(value_at(one)),
        ),
        (arena.value_type_base(BaseType::Integer), Ok(value_at(zero))),
        (arena.value_type_base(BaseType::String), Ok(value_at(zero))),
        (
            arena.value_type_base(BaseType::Numeric),
            Err(UnadmittedFormer::NumericAtom),
        ),
        (unit, Ok(value_at(zero))),
        (arena.value_type_thunk(returner), Ok(value_at(zero))),
        (arena.value_type_product(&[unit, unit]), Ok(value_at(zero))),
        (arena.value_type_sum(&[unit, unit]), Ok(value_at(zero))),
        (small, Ok(value_at(one))),
        (arena.value_type_lift(unit, level(one)), Ok(value_at(one))),
        (
            arena.value_type_element(code, Level::zero()),
            Ok(value_at(zero)),
        ),
        (arena.value_type_static_pi(small, small), Ok(value_at(one))),
    ];

    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[small]);
    for (value_type, answer) in rows {
        let expected = answer.map_err(|former| CheckRefusal::OutOfFragment {
            at: CoreNode::Type(TypeNode::Value(value_type)),
            former,
        });
        assert_eq!(
            classified(&mut context, value_type),
            expected,
            "every value-type former forms at its classifier or is refused by name"
        );
    }
    let atom = context
        .arena_mut()
        .value_type_abstract(ConstantIndex::from(0_usize));
    assert_eq!(
        classified(&mut context, atom),
        Err(CheckRefusal::NotAnAbstractType(ConstantIndex::from(
            0_usize
        ))),
        "a sealed atom no abstract type declares is refused by name"
    );
}

#[test]
fn every_comp_type_constructor_has_a_formation_rule()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let negative = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let returner = arena.comp_type_returner(unit);
    let code = arena.value_constant(ConstantIndex::from(1_usize));
    let zero = LevelConstant::from(0_u64);
    let rows = [
        (returner, comp_at(zero)),
        (arena.comp_type_arrow(unit, returner), comp_at(zero)),
        (
            arena.comp_type_pi(small, returner),
            comp_at(LevelConstant::from(1_u64)),
        ),
        (arena.comp_type_element(code, Level::zero()), comp_at(zero)),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[small, negative]);
    for (comp_type, classifier) in rows {
        assert_eq!(
            classified_comp(&mut context, comp_type),
            Ok(classifier),
            "every computation-type former forms at its classifier"
        );
    }
}

/// Every form the fragment refuses is refused under a name the caller
/// matches on, never under prose.
#[test]
fn unsupported_forms_have_nominal_kinds()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let top = Level::constant(LevelConstant::from(u64::MAX));
    let rows = [
        (
            arena.value_type_base(BaseType::Numeric),
            UnadmittedFormer::NumericAtom,
        ),
        (
            arena.value_type_universe(Sort::Parameter(SortParameter::from(0_u32)), Level::zero()),
            UnadmittedFormer::SortParameter,
        ),
        (
            arena.value_type_universe(Sort::Ground(GroundSort::Value), top),
            UnadmittedFormer::TopUniverse,
        ),
        (
            arena.value_type_lift(unit, Level::zero()),
            UnadmittedFormer::TypeLift,
        ),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (value_type, former) in rows {
        assert_eq!(
            form_value_type(&mut context, value_type),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(value_type)),
                former,
            }),
            "the refusal names the form"
        );
    }
}

#[test]
fn arrow_forms_at_the_join_of_its_premise_levels()
{
    let mut arena = CoreArena::new();
    let one = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let two = arena.value_type_universe(
        Sort::Ground(GroundSort::Value),
        level(LevelConstant::from(1_u64)),
    );
    let returns_two = arena.comp_type_returner(two);
    let returns_one = arena.comp_type_returner(one);
    let higher_codomain = arena.comp_type_arrow(one, returns_two);
    let higher_domain = arena.comp_type_arrow(two, returns_one);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = Ok(comp_at(LevelConstant::from(2_u64)));
    assert_eq!(classified_comp(&mut context, higher_codomain), expected);
    assert_eq!(
        classified_comp(&mut context, higher_domain),
        expected,
        "the join is symmetric in its premises"
    );
}

#[test]
fn effect_operation_types_participate_in_formation_levels_and_scope()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let high = arena.value_type_universe(
        Sort::Ground(GroundSort::Value),
        level(LevelConstant::from(2_u64)),
    );
    let high_signature = EffectSig::new(EffectName::from("Codes"), [EffectOp {
        name: OperationName::from("send"),
        payload: high,
        reply: unit,
    }])
    .expect("one operation");
    let high_returner =
        arena.comp_type_returner_with_effects(unit, EffectRow::singleton(high_signature));
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(code, Level::zero());
    let scoped_signature = EffectSig::new(EffectName::from("State"), [EffectOp {
        name: OperationName::from("get"),
        payload: unit,
        reply: decoded,
    }])
    .expect("one operation");
    let scoped_returner =
        arena.comp_type_returner_with_effects(unit, EffectRow::singleton(scoped_signature));
    let pi = arena.comp_type_pi(small, scoped_returner);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        classified_comp(&mut context, high_returner),
        Ok(comp_at(LevelConstant::from(3_u64))),
        "an operation payload contributes its level even when the returned value is Unit"
    );
    assert_eq!(
        classified_comp(&mut context, pi),
        Ok(comp_at(LevelConstant::from(1_u64)))
    );
    assert_eq!(
        form_comp_type(&mut context, scoped_returner),
        Err(CheckRefusal::UnboundIndex {
            at: code,
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
            depth: gandr_core_term::BinderDepth::from(0_usize)
        }),
        "forming the enclosing Pi does not discharge a row's free code variable outside that binder"
    );
}

#[test]
fn abstract_sort_raises_the_exact_variant()
{
    let mut arena = CoreArena::new();
    let universe =
        arena.value_type_universe(Sort::Parameter(SortParameter::from(0_u32)), Level::zero());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        form_value_type(&mut context, universe),
        Err(CheckRefusal::OutOfFragment {
            at: CoreNode::Type(TypeNode::Value(universe)),
            former: UnadmittedFormer::SortParameter,
        }),
        "a universe over a sort parameter has no ground reading"
    );
}

/// The dependent pair binds its first component over its second and forms
/// at the join of their levels, where the eager product over the same
/// factors mentions a variable nothing binds; a sealed atom no abstract
/// type declares is refused by name.
#[test]
fn the_dependent_pair_forms_at_the_join_of_its_levels()
{
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let sealed = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound, Level::zero());
    let sigma = arena.value_type_sigma(small, decoded);
    let product = arena.value_type_product(&[small, decoded]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        classified(&mut context, sigma),
        Ok(value_at(LevelConstant::from(1_u64))),
        "the first factor is a universe at level one, the second a type at zero"
    );
    assert_eq!(
        form_value_type(&mut context, product),
        Err(CheckRefusal::UnboundIndex {
            at: bound,
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
            depth: gandr_core_term::BinderDepth::from(0_usize),
        }),
        "the same factors without the binder mention a variable nothing binds"
    );
    assert_eq!(
        form_value_type(&mut context, sealed),
        Err(CheckRefusal::NotAnAbstractType(ConstantIndex::from(
            0_usize
        ))),
        "an atom forms only once its abstract type is admitted"
    );
}

#[test]
fn the_dependent_arrow_forms_at_the_join_of_its_levels()
{
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound, Level::zero());
    let returner = arena.comp_type_returner(decoded);
    let pi = arena.comp_type_pi(small, returner);
    let thunked = arena.value_type_thunk(pi);
    let arrow = arena.comp_type_arrow(small, returner);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        classified_comp(&mut context, pi),
        Ok(comp_at(LevelConstant::from(1_u64))),
        "the domain is a universe at level one, the codomain a type at zero"
    );
    assert_eq!(
        classified(&mut context, thunked),
        Ok(value_at(LevelConstant::from(1_u64))),
        "and it forms beneath a thunk"
    );
    assert_eq!(
        form_comp_type(&mut context, arrow),
        Err(CheckRefusal::UnboundIndex {
            at: bound,
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
            depth: gandr_core_term::BinderDepth::from(0_usize),
        }),
        "the same children without the binder mention a variable nothing binds"
    );
}

#[test]
fn an_unadmitted_former_beneath_an_arrow_is_found()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let numeric = arena.value_type_base(BaseType::Numeric);
    let result = arena.comp_type_returner(numeric);
    let arrow = arena.comp_type_arrow(unit, result);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        form_comp_type(&mut context, arrow),
        Err(CheckRefusal::OutOfFragment {
            at: CoreNode::Type(TypeNode::Value(numeric)),
            former: UnadmittedFormer::NumericAtom,
        }),
        "formation reaches every node, not only the root"
    );
}

#[test]
fn a_dangling_type_is_refused_as_a_fault()
{
    let mut arena = CoreArena::new();
    let dangling = dangling_value_type();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let refused = form_value_type(&mut context, dangling);
    assert_eq!(
        refused,
        Err(CheckRefusal::DanglingNode {
            node: CoreNode::Type(TypeNode::Value(dangling)),
        }),
        "an id the arena does not hold is refused rather than read"
    );
}

/// A step of a generated type: a postfix program over a stack of value
/// types and computation types, each carrying the level it is formed at.
#[derive(Clone, Copy, Debug)]
enum Step
{
    /// Push the integer atom.
    Integer,
    /// Push the unit type.
    Unit,
    /// Push the universe of the value sort, or of the computation sort, at
    /// a small level.
    Universe(bool, u8),
    /// Push the decode of the binder of the context counted round by the
    /// number held.
    Decode(u8),
    /// Pop a value type and push its returner.
    Returner,
    /// Pop a computation type and push its thunk type.
    Thunk,
    /// Pop a value type and a computation type and push their arrow.
    Arrow,
    /// Lift the value type on top to one level above its own.
    Lift,
}

/// The step strategy.
///
/// # Specification
/// - requires: nothing.
/// - ensures: generated steps use the admitted eight constructors, with
///   universe levels below three.
/// - panics: none.
/// - executable: none — the constructor holds no generated value; the
///   obligation ranges over future generation and shrinking.
///
/// # Adequacy
/// - hypothesis: L1 — programs of one to twenty-three generated steps over one
///   to three universe binders are observed by their independently constructed
///   classifier and by weakening; this bounds the generation evidence rather
///   than claiming exhaustive random coverage.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::weakening_preserves_formation`
fn step() -> impl proptest::strategy::Strategy<Value = Step>
{
    use proptest::prelude::Just;
    use proptest::prelude::any;
    use proptest::prop_oneof;
    use proptest::strategy::Strategy as _;
    prop_oneof![
        Just(Step::Integer),
        Just(Step::Unit),
        (any::<bool>(), 0_u8 .. 3_u8).prop_map(|(positive, at)| Step::Universe(positive, at)),
        any::<u8>().prop_map(Step::Decode),
        Just(Step::Returner),
        Just(Step::Thunk),
        Just(Step::Arrow),
        Just(Step::Lift),
    ]
}

/// The generated value type and the level a reference reads off its
/// construction, over a context of value universes at `levels`.
struct Generated
{
    /// The value type.
    root: ValueTypeId,
    /// The level the construction gives it.
    level: Level,
}

/// A level a generated binder's universe stands at: zero to two.
///
/// # Specification
/// - requires: nothing.
/// - ensures: generated and shrunk levels are zero, one or two.
/// - panics: none.
/// - executable: none — no level is sampled until the returned strategy is run;
///   construction cannot inspect all its future samples.
///
/// # Adequacy
/// - hypothesis: L1 — lists of one to three bounded levels supply the universes
///   used by the reference classifier and weakening properties; these separate
///   an incorrect level interpretation, not distribution.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::weakening_preserves_formation`
fn small_level() -> impl proptest::strategy::Strategy<Value = LevelConstant>
{
    use proptest::strategy::Strategy as _;
    (0_u64 .. 3_u64).prop_map(LevelConstant::from)
}

/// Build `steps` over a context of binders, the `i`th from the innermost
/// a value universe at `levels[i]`, skipping every step the stacks cannot
/// take, and close the result with returners and thunks into one value
/// type.
///
/// # Specification
/// - requires: at most three binder levels below three and fewer than
///   twenty-four steps, as produced by the property strategies.
/// - ensures: the root resolves in `arena` and its natural level equals the
///   level computed alongside the postfix construction. The predicate checks
///   resolution; the property witnesses compare the level.
/// - panics: a level or binder index exceeds the bounded recipe domain.
///
/// # Adequacy
/// - hypothesis: L1 — bounded postfix programs compare formation with their
///   construction-derived level; weakening separates binder-offset changes. No
///   arbitrary-depth or unbounded-level claim is made.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::weakening_preserves_formation`
#[spec(
        requires: levels.len() < 4 && steps.len() < 24
            && levels.iter().all(|level| u64::from(*level) < 3),
        ensures: |ret| arena.value_type(ret.root).is_some(),
    )]
fn build(
    arena: &mut CoreArena,
    levels: &[LevelConstant],
    steps: &[Step],
) -> Generated
{
    let mut values: Vec<(ValueTypeId, Level)> = Vec::new();
    let mut comps: Vec<(CompTypeId, Level)> = Vec::new();
    for &step in steps {
        match step {
            Step::Integer => {
                values.push((arena.value_type_base(BaseType::Integer), Level::zero()));
            },
            Step::Unit => values.push((arena.value_type_unit(), Level::zero())),
            Step::Universe(positive, at) => {
                let sort = if positive {
                    GroundSort::Value
                }
                else {
                    GroundSort::Computation
                };
                let own = level(LevelConstant::from(u64::from(at)));
                let above = own.succ().expect("a small level has a successor");
                values.push((arena.value_type_universe(Sort::Ground(sort), own), above));
            },
            Step::Decode(pick) => {
                if let Some(position) = usize::from(pick).checked_rem(levels.len())
                    && let Some(&at) = levels.get(position)
                {
                    let index = DeBruijnIndex::from(u32::try_from(position).expect("small"));
                    let code = arena.value_variable(Zone::Intuitionistic, index);
                    let own = level(at);
                    values.push((arena.value_type_element(code, own.clone()), own));
                }
            },
            Step::Returner => {
                if let Some((result, own)) = values.pop() {
                    comps.push((arena.comp_type_returner(result), own));
                }
            },
            Step::Thunk => {
                if let Some((body, own)) = comps.pop() {
                    values.push((arena.value_type_thunk(body), own));
                }
            },
            Step::Arrow => {
                if let (Some(&(domain, ref from)), Some(&(codomain, ref to))) =
                    (values.last(), comps.last())
                {
                    let joined = from.max(to);
                    let arrow = arena.comp_type_arrow(domain, codomain);
                    values.pop();
                    comps.pop();
                    comps.push((arrow, joined));
                }
            },
            Step::Lift => {
                if let Some((inner, own)) = values.pop() {
                    let above = own.succ().expect("a generated level has a successor");
                    values.push((arena.value_type_lift(inner, above.clone()), above));
                }
            },
        }
    }
    let (mut root, mut at) = values
        .pop()
        .unwrap_or_else(|| (arena.value_type_unit(), Level::zero()));
    while let Some((body, own)) = comps.pop() {
        let arrow = arena.comp_type_arrow(root, body);
        at = at.max(&own);
        root = arena.value_type_thunk(arrow);
    }
    Generated { root, level: at }
}

/// Open one binder per level of `levels`, outermost first, each a value
/// universe at its level.
///
/// # Specification
/// - requires: each supplied level denotes a universe.
/// - ensures: one intuitionistic binder is added per supplied level, in reverse
///   input order so index zero reads the first supplied level.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — one to three generated binders and up to two fresh
///   binders expose the classifier before and after weakening; wrong order or
///   missing binders changes a decode or its level.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::weakening_preserves_formation`
#[spec(
        captures: depth = usize::from(context.depth(Zone::Intuitionistic)),
        ensures: usize::from(context.depth(Zone::Intuitionistic)).checked_sub(depth) == Some(levels.len()),
    )]
fn open_universes(
    context: &mut CheckingContext<'_>,
    levels: &[LevelConstant],
)
{
    for &at in levels.iter().rev() {
        let universe = context
            .arena_mut()
            .value_type_universe(Sort::Ground(GroundSort::Value), level(at));
        context.binders().open(Zone::Intuitionistic, universe);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn every_type_has_exactly_one_classifier(
        levels in vec(small_level(), 1 .. 4),
        steps in vec(step(), 1 .. 24),
    )
    {
        let mut arena = CoreArena::new();
        let generated = build(&mut arena, &levels, &steps);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        open_universes(&mut context, &levels);
        let expected = Classifier { sort: GroundSort::Value, level: generated.level };
        let first = classified(&mut context, generated.root);
        let second = classified(&mut context, generated.root);
        prop_assert_eq!(&first, &Ok(expected), "formation answers the classifier the construction gives");
        prop_assert_eq!(first, second, "and answers it again");
    }

    #[test]
    fn weakening_preserves_formation(
        levels in vec(small_level(), 1 .. 4),
        fresh in vec(small_level(), 0 .. 3),
        steps in vec(step(), 1 .. 24),
    )
    {
        let mut arena = CoreArena::new();
        let generated = build(&mut arena, &levels, &steps);
        let amount = Binders::from(u32::try_from(fresh.len()).expect("small"));
        let weakened = shift_value_type(&mut arena, generated.root, amount).settle(&mut arena);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        open_universes(&mut context, &levels);
        let before = classified(&mut context, generated.root);
        open_universes(&mut context, &fresh);
        let after = classified(&mut context, weakened);
        prop_assert_eq!(before, after, "a type shifted past fresh binders forms at its classifier still");
    }
}

#[test]
fn a_path_code_is_closed_first_order_and_inhabited()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let lone = arena.value_type_sum(&[unit]);
    let void = arena.value_type_sum(&[]);
    let mixed = arena.value_type_product(&[integer, lone]);
    let hollow = arena.value_type_product(&[integer, void]);
    for admitted in [integer, mixed] {
        let code = arena.value_quote(admitted);
        assert_eq!(
            path_code(&arena, code),
            Ok(admitted),
            "a base atom and a product over a sum of one summand are path codes"
        );
    }
    for refused in [void, hollow] {
        let code = arena.value_quote(refused);
        assert_eq!(
            path_code(&arena, code),
            Err(CheckRefusal::PathCode(code)),
            "the empty sum is no path code, alone or inside a product"
        );
    }
}

/// A stack, a staged type, a kept type, a capability's operations and a
/// value held at a world each stand at the level of what they carry; a world
/// capability, a buffer and a run stand at zero; a family or codata
/// declaration not in scope is refused by name.
#[test]
fn each_carrying_former_stands_at_the_level_of_what_it_carries()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;
    use gandr_core_term::world::World;
    use gandr_core_term::world::WorldType;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;

    use super::level_of;

    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let unit = arena.value_type_unit();
    let returns_small = arena.comp_type_returner(small);
    let returns_unit = arena.comp_type_returner(unit);
    let operations = EffectSig::new(EffectName::from("Probe"), [EffectOp {
        name: OperationName::from("poke"),
        payload: small,
        reply: unit,
    }])
    .expect("one operation");
    let one = Level::zero().succ().expect("one is below the top");
    let session = arena.value_unit();
    let rows = [
        (
            arena.value_type_stack(returns_small, returns_unit),
            one.clone(),
            "a stack",
        ),
        (
            arena.value_type_staged(small, Stage::At(StageId::from(0_usize))),
            one.clone(),
            "a staged type",
        ),
        (
            arena.value_type_kept(small, Region::Scoped(RegionDepth::from(1_u32))),
            one.clone(),
            "a kept type",
        ),
        (
            arena.value_type_capability(
                EffectRow::singleton(operations),
                CapabilityGrade::Durable,
                Region::Scoped(RegionDepth::from(1_u32)),
            ),
            one.clone(),
            "a capability",
        ),
        (
            arena.value_type_world(WorldType::At {
                inner: small,
                world: World::Host,
            }),
            one,
            "a value held at a world",
        ),
        (
            arena.value_type_world(WorldType::Capability(World::Host)),
            Level::zero(),
            "a world capability",
        ),
        (arena.value_type_buffer(), Level::zero(), "a buffer"),
        (arena.value_type_run(session), Level::zero(), "a run"),
    ];
    let family = arena.value_type_data(ConstantIndex::from(4_usize), Vec::new());
    let codata = arena.comp_type_codata(ConstantIndex::from(5_usize), Vec::new());
    let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (ty, level, former) in rows {
        assert_eq!(
            level_of(&context, TypeNode::Value(ty)),
            Ok(level),
            "{former}"
        );
    }
    assert_eq!(
        level_of(&context, TypeNode::Value(family)),
        Err(CheckRefusal::NotADataType(ConstantIndex::from(4_usize))),
        "a family not in scope is no data type"
    );
    assert!(
        matches!(
            level_of(&context, TypeNode::Computation(codata)),
            Err(CheckRefusal::Codata {
                fault: crate::codata::CodataFault::Undeclared,
                ..
            })
        ),
        "a codata type not in scope is undeclared"
    );
}
