use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use super::BinderDistance;
use super::CriticalPeak;
use super::OperationRank;
use super::PRESENTATION_CODE;
use super::PeakSearch;
use super::SidePosition;
use super::SymbolKind;
use super::TheoryNode;
use super::TheoryRule;
use super::TheoryRuleFault;
use super::TheoryRuleRefusal;
use super::TheoryRules;
use super::TheorySymbol;
use super::presentation_code;
use crate::ConstructorTag;
use crate::Literal;
use crate::StringLiteral;
use crate::TermArena;
use crate::ValueId;
use crate::ValueTypeId;
use crate::base::BaseType;
use crate::presented::FieldCount;
use crate::presented::RewriteFuel;
use crate::presented::RuleIndex;
use crate::presented::RuleVariable;
use crate::term::ConstantIndex;

/// The symbol node at a table position.
macro_rules! s {
    ($symbol:literal) => {
        TheoryNode::Symbol(<TheorySymbol as From<usize>>::from($symbol))
    };
}

/// The variable node of an ordinal.
macro_rules! v {
    ($ordinal:literal) => {
        TheoryNode::Variable(<RuleVariable as From<u32>>::from($ordinal))
    };
}

/// The instantiation of a variable's ordinal at an argument count.
macro_rules! i {
    ($ordinal:literal, $count:literal) => {
        TheoryNode::Instance(
            <RuleVariable as From<u32>>::from($ordinal),
            <FieldCount as From<usize>>::from($count),
        )
    };
}

/// An operation of an arity at a rank.
macro_rules! operation {
    ($rank:literal, $arity:literal) => {
        (
            SymbolKind::Operation(<OperationRank as From<u32>>::from($rank)),
            <FieldCount as From<usize>>::from($arity),
        )
    };
}

/// The refusal at a rule for a fault.
macro_rules! refused {
    ($rule:literal, $fault:expr) => {
        Err::<(), TheoryRuleRefusal>(TheoryRuleRefusal {
            rule: <RuleIndex as From<usize>>::from($rule),
            fault: $fault,
        })
    };
}

/// The rule rewriting `left` to `right`.
///
/// # Specification
/// trivial.
fn rule(
    left: &[TheoryNode],
    right: &[TheoryNode],
) -> TheoryRule
{
    TheoryRule::new(left.into(), right.into())
}

/// Ample fuel.
///
/// # Specification
/// trivial.
fn fuel() -> RewriteFuel
{
    RewriteFuel::from(1_u64 << 20)
}

#[test]
fn the_presentation_code_is_recognised_by_its_table()
{
    let mut arena = TermArena::new();
    let own = ConstantIndex::from(3_usize);
    let string = arena.value_type_base(BaseType::String);
    let recursion = arena.value_type_data(own, Vec::new());
    let elsewhere = arena.value_type_data(ConstantIndex::from(2_usize), Vec::new());
    let table = |string: ValueTypeId, recursion: ValueTypeId| -> Vec<Vec<ValueTypeId>> {
        PRESENTATION_CODE
            .iter()
            .map(|&(strings, recursions)| {
                let mut fields = vec![string; strings];
                fields.extend(core::iter::repeat_n(recursion, recursions));
                fields
            })
            .collect()
    };
    let code = table(string, recursion);
    assert!(bool::from(presentation_code(&arena, own, &code)));
    assert!(
        !bool::from(presentation_code(&arena, own, &code[.. code.len() - 1])),
        "a constructor short"
    );
    let mut misread = code;
    misread[3][0] = recursion;
    assert!(
        !bool::from(presentation_code(&arena, own, &misread)),
        "a name read as a recursion"
    );
    assert!(
        !bool::from(presentation_code(&arena, own, &table(string, elsewhere))),
        "recurring into another declaration"
    );
}

#[test]
fn a_unit_law_converges_and_a_second_unit_parts_from_it()
{
    // mul = 0, e = 1.
    let symbols = vec![operation!(1, 2), operation!(1, 0)];
    let unit = rule(&[s!(0), s!(1), v!(0)], &[v!(0)]);
    let rules = TheoryRules::new(symbols.clone(), vec![unit.clone()]);
    assert_eq!(rules.decide(&mut fuel()), Ok(()));
    let twin = TheoryRules::new(symbols, vec![unit, rule(&[s!(0), s!(1), v!(0)], &[s!(1)])]);
    assert_eq!(
        twin.decide(&mut fuel()),
        refused!(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "the second law rewrites the unit's call apart from it"
    );
}

#[test]
fn a_groups_completion_replays_from_its_peaks()
{
    // mul = 0, inv = 1, e = 2.
    let symbols = vec![operation!(1, 2), operation!(1, 1), operation!(0, 0)];
    let inverse = rule(&[s!(0), s!(1), v!(0), v!(0)], &[s!(2)]);
    let involution = rule(&[s!(1), s!(1), v!(0)], &[v!(0)]);
    let written = TheoryRules::new(symbols, vec![inverse, involution]);
    assert_eq!(
        written.decide(&mut fuel()),
        refused!(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "the inverse law's argument rewrites apart under the involution"
    );
    let right_inverse = rule(&[s!(0), v!(0), s!(1), v!(0)], &[s!(2)]);
    let peak = CriticalPeak {
        outer: RuleIndex::from(0_usize),
        position: SidePosition::from(1_usize),
        inner: RuleIndex::from(1_usize),
    };
    let mut search = PeakSearch::default();
    assert_eq!(
        written.peak_of(&right_inverse, &mut search, &mut fuel()),
        Ok(Some(peak)),
        "the derived rule joins the inverse law overlapped by the involution"
    );
    let mut completed = written.clone();
    completed.derive(right_inverse.clone(), peak);
    assert_eq!(completed.decide(&mut fuel()), Ok(()));
    let mut misnamed = written.clone();
    misnamed.derive(right_inverse, CriticalPeak {
        outer: RuleIndex::from(1_usize),
        position: SidePosition::from(1_usize),
        inner: RuleIndex::from(1_usize),
    });
    assert_eq!(
        misnamed.decide(&mut fuel()),
        refused!(2, TheoryRuleFault::NoPeak),
        "the involution's own overlap joins, so it derives nothing"
    );
    let unreached = rule(&[s!(0), v!(0), s!(1), v!(0)], &[v!(0)]);
    assert_eq!(
        written.peak_of(&unreached, &mut search, &mut fuel()),
        Ok(None),
        "a search left holding the last pair still finds no peak for a side no pair reaches"
    );
    let mut overstated = written;
    overstated.derive(unreached, peak);
    assert_eq!(
        overstated.decide(&mut fuel()),
        refused!(2, TheoryRuleFault::NoPeak),
        "a side the peak does not reach"
    );
}

#[test]
fn a_rule_the_ranks_do_not_decrease_is_unoriented()
{
    let calls = rule(&[s!(0), v!(0)], &[s!(1), v!(0)]);
    let level = TheoryRules::new(vec![operation!(1, 1), operation!(1, 1)], vec![
        calls.clone(),
    ]);
    assert_eq!(
        level.decide(&mut fuel()),
        refused!(0, TheoryRuleFault::Unoriented)
    );
    let ranked = TheoryRules::new(vec![operation!(2, 1), operation!(1, 1)], vec![calls]);
    assert_eq!(ranked.decide(&mut fuel()), Ok(()));
    let associativity = rule(&[s!(0), s!(0), v!(0), v!(1), v!(2)], &[
        s!(0),
        v!(0),
        s!(0),
        v!(1),
        v!(2),
    ]);
    let product = TheoryRules::new(vec![operation!(1, 2)], vec![associativity]);
    assert_eq!(product.decide(&mut fuel()), Ok(()), "associativity orients");
}

#[test]
fn a_malformed_rule_is_refused_by_its_fault()
{
    let symbols = vec![
        operation!(1, 1),
        (SymbolKind::Constructor, FieldCount::from(1_usize)),
    ];
    let decided = |left: &[TheoryNode], right: &[TheoryNode]| {
        TheoryRules::new(symbols.clone(), vec![rule(left, right)]).decide(&mut fuel())
    };
    let malformed = refused!(0, TheoryRuleFault::Malformed);
    assert_eq!(decided(&[v!(0)], &[v!(0)]), malformed, "a variable head");
    assert_eq!(
        decided(&[s!(1), v!(0)], &[v!(0)]),
        malformed,
        "a constructor head"
    );
    assert_eq!(decided(&[s!(0)], &[s!(0)]), malformed, "an argument short");
    assert_eq!(
        decided(&[s!(0), v!(1)], &[v!(1)]),
        malformed,
        "a skipped variable"
    );
    assert_eq!(
        decided(&[s!(2), v!(0)], &[v!(0)]),
        malformed,
        "an unknown symbol"
    );
    assert_eq!(
        decided(&[s!(0), v!(0)], &[v!(1)]),
        refused!(0, TheoryRuleFault::Unbound)
    );
}

#[test]
fn a_let_rule_converges_and_beta_is_unoriented()
{
    // let = 0, app = 1, lam = 2, zero = 3.
    let symbols = vec![
        operation!(1, 2),
        operation!(1, 2),
        operation!(1, 1),
        operation!(0, 0),
    ];
    let decided =
        |rules: Vec<TheoryRule>| TheoryRules::new(symbols.clone(), rules).decide(&mut fuel());
    // let(u, t) ==> t(u)
    let zeta = rule(&[s!(0), v!(0), v!(1)], &[i!(1, 1), v!(0)]);
    assert_eq!(decided(vec![zeta.clone()]), Ok(()));
    // app(zero, u) ==> u
    let apart = rule(&[s!(1), s!(3), v!(0)], &[v!(0)]);
    assert_eq!(
        decided(vec![zeta.clone(), apart]),
        Ok(()),
        "a first-order rule overlapping no left side of `let` converges beside it"
    );
    // app(lam(t), u) ==> t(u)
    let beta = rule(&[s!(1), s!(2), v!(0), v!(1)], &[i!(0, 1), v!(1)]);
    assert_eq!(
        decided(vec![beta]),
        refused!(0, TheoryRuleFault::Unoriented),
        "β's variable stands under `lam`, not as an argument of `app`"
    );
    // let(zero, t) ==> t(zero)
    let at_zero = rule(&[s!(0), s!(3), v!(0)], &[i!(0, 1), s!(3)]);
    assert_eq!(
        decided(vec![zeta.clone(), at_zero]),
        Ok(()),
        "a second-order rule's critical pair joins: both reducts are `t(zero)`"
    );
    // let(zero, t) ==> zero
    let to_zero = rule(&[s!(0), s!(3), v!(0)], &[s!(3)]);
    assert_eq!(
        decided(vec![zeta, to_zero]),
        refused!(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "`t(zero)` and `zero` part"
    );
    assert_eq!(
        decided(vec![rule(&[s!(0), v!(0), i!(1, 1), s!(3)], &[v!(0)])]),
        refused!(0, TheoryRuleFault::Malformed),
        "an instantiation on a left side at anything but bound names"
    );
    assert_eq!(
        decided(vec![rule(&[s!(0), v!(0), v!(1)], &[i!(2, 1), v!(0)])]),
        refused!(0, TheoryRuleFault::Unbound),
        "an instantiation of a variable the left side does not bind"
    );
}

/// #2115: a metavariable applied on a left side to the names its
/// abstractions bind is a pattern; the order holds it under the abstraction
/// it is applied in, and an overlap through it is found.
#[test]
fn a_pattern_on_the_left_is_read_and_decided_2115()
{
    // run = 0, get = 1, the binding field = 2, the bound occurrences counting
    // none and one binder = 3 and 4, zero = 5.
    let symbols = vec![
        operation!(1, 2),
        operation!(1, 1),
        (SymbolKind::Field, FieldCount::from(1_usize)),
        (
            SymbolKind::Bound(BinderDistance::from(0_usize)),
            FieldCount::from(0_usize),
        ),
        (
            SymbolKind::Bound(BinderDistance::from(1_usize)),
            FieldCount::from(0_usize),
        ),
        (SymbolKind::Constructor, FieldCount::from(0_usize)),
    ];
    let decided =
        |rules: Vec<TheoryRule>| TheoryRules::new(symbols.clone(), rules).decide(&mut fuel());
    // run(bind x . k(x), u) ==> k(u)
    let applied = rule(&[s!(0), s!(2), i!(0, 1), s!(3), v!(1)], &[i!(0, 1), v!(1)]);
    assert_eq!(
        decided(vec![applied]),
        Ok(()),
        "`run` holds `k` under the abstraction it applies it in, and overlaps nothing"
    );
    // get(bind s . get(bind t . k(s, t))) ==> get(bind s . k(s, s))
    let get_get = rule(&[s!(1), s!(2), s!(1), s!(2), i!(0, 2), s!(4), s!(3)], &[
        s!(1),
        s!(2),
        i!(0, 2),
        s!(3),
        s!(3),
    ]);
    assert_eq!(
        decided(vec![get_get]),
        Ok(()),
        "get-get's inner `get` is an instance of its own left side through the pattern, and the \
         pair joins at `get(bind s . k(s, s, s))`"
    );
    let malformed = refused!(0, TheoryRuleFault::Malformed);
    assert_eq!(
        decided(vec![rule(&[s!(0), s!(2), i!(0, 1), s!(5), v!(1)], &[
            i!(0, 1),
            v!(1)
        ])]),
        malformed,
        "a metavariable applied to a constructor is no pattern"
    );
    assert_eq!(
        decided(vec![rule(
            &[s!(1), s!(2), s!(1), s!(2), i!(0, 2), s!(3), s!(3)],
            &[s!(1), s!(2), i!(0, 2), s!(3), s!(3)]
        )]),
        malformed,
        "nor one applied to one name twice"
    );
    // ext(m, bind x . n) ==> n, `n` leaving the abstraction, beside
    // ret : (a : S) --> C and ext : (m : C, k : pi+ (x : V) . C) --> C.
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let rule_tag = ConstructorTag::from(super::tag::RULE);
    let conditioned = |unit: &str| {
        let mut code = Code::new();
        let (m, n) = (code.var(literal("m")), code.var(literal("n")));
        let over = code.lam(literal("x"), n);
        let left = code.app(literal("ext"), &[m, over]);
        let leak = code.text(literal("leak"));
        let (sorts, operations) = code.monad(literal(unit));
        let presentation =
            code.presenting(sorts, operations, vec![(rule_tag, vec![leak, left, n])]);
        TheoryRules::read(&code.arena, presentation).map(|read| {
            read.rules()
                .iter()
                .map(|rule| rule.conditioned)
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(
        conditioned("V"),
        Ok(vec![true]),
        "`ret` takes a value at the sort `ext`'s continuation binds, so a term names a bound \
         variable and `n` leaving `bind x .` fires only where its instance names no `x`"
    );
    assert_eq!(
        conditioned("C"),
        Ok(vec![false]),
        "where no port takes a bound variable no term names one"
    );
}

/// #2328: a relative monad's associativity overlaps itself and both unit
/// laws, its right side substituting under the binder it writes; every pair
/// joins in the second-order reading.
#[test]
fn a_relative_monads_laws_join_their_overlaps_2328()
{
    // ext = 0, ret = 1, the binding field = 2, the bound occurrence = 3.
    let symbols = vec![
        operation!(1, 2),
        operation!(0, 1),
        (SymbolKind::Field, FieldCount::from(1_usize)),
        (
            SymbolKind::Bound(BinderDistance::from(0_usize)),
            FieldCount::from(0_usize),
        ),
    ];
    let decided =
        |rules: Vec<TheoryRule>| TheoryRules::new(symbols.clone(), rules).decide(&mut fuel());
    // ext(ret(a), k) ==> k(a)
    let unit_left = rule(&[s!(0), s!(1), v!(0), v!(1)], &[i!(1, 1), v!(0)]);
    // ext(m, bind x . ret(x)) ==> m
    let unit_right = rule(&[s!(0), v!(0), s!(2), s!(1), s!(3)], &[v!(0)]);
    // ext(ext(m, k), l) ==> ext(m, bind x . ext(k(x), l))
    let assoc = rule(&[s!(0), s!(0), v!(0), v!(1), v!(2)], &[
        s!(0),
        v!(0),
        s!(2),
        s!(0),
        i!(1, 1),
        s!(3),
        v!(2),
    ]);
    assert_eq!(
        decided(vec![assoc.clone()]),
        Ok(()),
        "associativity overlaps itself at its inner `ext`, both reducts normalizing to \
         `ext(m, bind x . ext(k(x), bind y . ext(l(y), n)))`"
    );
    assert_eq!(
        decided(vec![unit_left.clone(), unit_right.clone(), assoc]),
        Ok(()),
        "with the unit laws, every pair joins"
    );
    // ext(ext(m, k), l) ==> ext(m, l), dropping `k`
    let lossy = rule(&[s!(0), s!(0), v!(0), v!(1), v!(2)], &[s!(0), v!(0), v!(2)]);
    assert_eq!(
        decided(vec![unit_left, unit_right, lossy]),
        refused!(2, TheoryRuleFault::Diverges(RuleIndex::from(0_usize))),
        "the lossy rule, overlapping the left unit law at its inner `ext`, parts in the \
         second-order reading: `l(a)` against `ext(k(a), l)`"
    );
}

/// #2966: in the second-order reading a closed term's rule instantiating a
/// variable fires by matching and substitution, below an operation and under
/// a binder too; a rule under a row does not fire in a program naming none.
#[test]
fn an_instantiating_rule_fires_by_substitution_2966()
{
    use super::NormalNode;
    use super::row::RowExtent;
    use super::row::RowLabel;
    use super::row::RuleRow;

    // app = 0, post = 1, z = 2, the binding field = 3, the bound occurrence
    // = 4, w = 5, lit = 6, int = 7.
    let symbols = vec![
        operation!(1, 2),
        operation!(0, 1),
        operation!(0, 0),
        (SymbolKind::Field, FieldCount::from(1_usize)),
        (
            SymbolKind::Bound(BinderDistance::from(0_usize)),
            FieldCount::from(0_usize),
        ),
        operation!(1, 2),
        operation!(0, 1),
        operation!(0, 1),
    ];
    // app(k, a) ==> k(a)
    let beta = rule(&[s!(0), v!(0), v!(1)], &[i!(0, 1), v!(1)]);
    // w(lit(n), k) ==> k(int(n))
    let literal = rule(&[s!(5), s!(6), v!(0), v!(1)], &[i!(1, 1), s!(7), v!(0)]);
    let rules = TheoryRules::new(symbols.clone(), vec![beta.clone(), literal]);
    assert_eq!(rules.decide(&mut fuel()), Ok(()));
    let normal = |rules: &TheoryRules, term: &[TheoryNode]| {
        rules
            .second_order_normal_form(term, &mut fuel())
            .expect("the term normalizes within its fuel")
            .map(Vec::from)
    };
    let symbol = |at: usize| NormalNode::Symbol(TheorySymbol::from(at));
    // app(bind v . post(v), z)
    let applied = [s!(0), s!(3), s!(1), s!(4), s!(2)];
    assert_eq!(
        normal(&rules, &applied),
        Some(vec![symbol(1), symbol(2)]),
        "β substitutes `z` for the field's variable: `post(z)`, not `k(z)`"
    );
    // app(bind v . w(lit(v), bind u . post(u)), z)
    let nested = [
        s!(0),
        s!(3),
        s!(5),
        s!(6),
        s!(4),
        s!(3),
        s!(1),
        s!(4),
        s!(2),
    ];
    assert_eq!(
        normal(&rules, &nested),
        Some(vec![symbol(1), symbol(7), symbol(2)]),
        "the literal rule fires below `app` under `v`, then β: `post(int(z))`"
    );
    let under = TheoryRules::new(symbols, vec![beta.under(RuleRow::new(
        vec![RowLabel::from(0_u32)],
        RowExtent::AtLeast,
    ))]);
    assert_eq!(
        normal(&under, &applied),
        Some(vec![
            symbol(0),
            symbol(3),
            symbol(1),
            NormalNode::Bound(BinderDistance::from(0_usize)),
            symbol(2),
        ]),
        "a rule under a row fires in no row a program naming no theory stands in"
    );
    assert_eq!(
        normal(&rules, &[s!(1), v!(0)]),
        None,
        "a term holding a variable is not closed"
    );
    assert_eq!(
        normal(&rules, &[s!(0), s!(2)]),
        None,
        "nor one ending early"
    );
}

/// #2272: read from a presentation, put-get instantiates its continuation at
/// the value `put` stores. While no operation returns that value's sort, the
/// variable is one of the rule's values and the rule is decided. Once `read`
/// returns it, the instantiation needs a cover the left side lacks.
#[test]
fn an_instantiation_at_a_value_selects_a_branch_2272()
{
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let tag = ConstructorTag::from;
    let state = |reads: bool| -> Result<Vec<Box<[RuleVariable]>>, TheoryRuleRefusal> {
        let mut code = Code::new();
        let [
            values,
            computations,
            get,
            put,
            read,
            stored,
            branch,
            observed,
            answer,
            put_get,
        ] = ["S", "C", "get", "put", "read", "s", "t", "c", "y", "putGet"]
            .map(|text| code.text(literal(text)));
        let continuation = code.text(literal("k"));
        let end = code.end();
        let computation_sort = code.node(tag(super::tag::SORT), vec![computations, end, end]);
        let sorts = code.node(tag(super::tag::SORT), vec![values, end, computation_sort]);
        let returns =
            |code: &mut Code, sort| code.node(tag(super::tag::PORT), vec![answer, sort, end, end]);
        let binder = code.node(tag(super::tag::PORT), vec![branch, values, end, end]);
        let branches = code.node(tag(super::tag::BOUND), vec![
            continuation,
            computations,
            end,
            binder,
            end,
        ]);
        let resumed = code.node(tag(super::tag::PORT), vec![
            continuation,
            computations,
            end,
            end,
        ]);
        let stores = code.node(tag(super::tag::PORT), vec![stored, values, end, resumed]);
        let observes = code.node(tag(super::tag::PORT), vec![
            observed,
            computations,
            end,
            end,
        ]);
        let mut operations = end;
        if reads {
            let reply = returns(&mut code, values);
            operations = code.node(tag(super::tag::OPER), vec![
                read, observes, reply, operations,
            ]);
        }
        let returned = returns(&mut code, computations);
        operations = code.node(tag(super::tag::OPER), vec![
            put, stores, returned, operations,
        ]);
        let returned = returns(&mut code, computations);
        operations = code.node(tag(super::tag::OPER), vec![
            get, branches, returned, operations,
        ]);
        // put(s, get(bind t . k(t))) ==> put(s, k(s))
        let value = code.var(literal("s"));
        let named = code.bvar(literal("t"));
        let pattern = code.inst(literal("k"), &[named]);
        let held = code.lam(literal("t"), pattern);
        let got = code.app(literal("get"), &[held]);
        let left = code.app(literal("put"), &[value, got]);
        let selected = code.inst(literal("k"), &[value]);
        let right = code.app(literal("put"), &[value, selected]);
        let presentation = code.presenting(sorts, operations, vec![(tag(super::tag::RULE), vec![
            put_get, left, right,
        ])]);
        let read = TheoryRules::read(&code.arena, presentation)?;
        let read_values = read
            .rules()
            .iter()
            .map(|rule| rule.values.clone())
            .collect::<Vec<_>>();
        read.decide(&mut fuel())?;
        Ok(read_values)
    };
    assert_eq!(
        state(false),
        Ok(vec![Box::from([RuleVariable::from(0_u32)])]),
        "`s` stands only at `put`'s port of `S`, which no operation returns, so `k(s)` selects \
         the branch `get` holds"
    );
    assert_eq!(
        state(true).map(|_| ()),
        refused!(0, TheoryRuleFault::Unoriented),
        "once `read` returns `S`, `s` is no value and `k(s)` needs a cover"
    );
}

/// Values of the presentation code minted into one arena.
struct Code
{
    /// The arena.
    arena: TermArena,
    /// The code's type.
    theory: ValueTypeId,
}

impl Code
{
    /// An empty arena with the code at position zero.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        let mut arena = TermArena::new();
        let theory = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        Self { arena, theory }
    }

    /// The string `text`.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &mut self,
        text: StringLiteral,
    ) -> ValueId
    {
        self.arena.value_literal(Literal::Text(text))
    }

    /// The constructor `tag` over `fields`.
    ///
    /// # Specification
    /// trivial.
    fn node(
        &mut self,
        tag: ConstructorTag,
        fields: Vec<ValueId>,
    ) -> ValueId
    {
        self.arena.value_constructor(self.theory, tag, fields)
    }

    /// The end of a chain.
    ///
    /// # Specification
    /// trivial.
    fn end(&mut self) -> ValueId
    {
        self.node(ConstructorTag::from(super::tag::END), Vec::new())
    }

    /// The variable `name`.
    ///
    /// # Specification
    /// trivial.
    fn var(
        &mut self,
        name: StringLiteral,
    ) -> ValueId
    {
        let name = self.text(name);
        self.node(ConstructorTag::from(super::tag::VAR), vec![name])
    }

    /// The operation `name` applied to `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn app(
        &mut self,
        name: StringLiteral,
        arguments: &[ValueId],
    ) -> ValueId
    {
        let mut chain = self.end();
        for &argument in arguments.iter().rev() {
            chain = self.node(ConstructorTag::from(super::tag::ARG), vec![argument, chain]);
        }
        let name = self.text(name);
        self.node(ConstructorTag::from(super::tag::APP), vec![name, chain])
    }

    /// The variable `name` instantiated at `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn inst(
        &mut self,
        name: StringLiteral,
        arguments: &[ValueId],
    ) -> ValueId
    {
        let mut chain = self.end();
        for &argument in arguments.iter().rev() {
            chain = self.node(ConstructorTag::from(super::tag::ARG), vec![argument, chain]);
        }
        let name = self.text(name);
        self.node(ConstructorTag::from(super::tag::INST), vec![name, chain])
    }

    /// The abstraction of the atom `atom` over `body`.
    ///
    /// # Specification
    /// trivial.
    fn abs(
        &mut self,
        atom: StringLiteral,
        body: ValueId,
    ) -> ValueId
    {
        let end = self.end();
        let chain = self.node(ConstructorTag::from(super::tag::ARG), vec![body, end]);
        let atom = self.text(atom);
        self.node(ConstructorTag::from(super::tag::ABS), vec![atom, chain])
    }

    /// The atom `atom`, named inside an abstraction of it.
    ///
    /// # Specification
    /// trivial.
    fn occ(
        &mut self,
        atom: StringLiteral,
    ) -> ValueId
    {
        let atom = self.text(atom);
        self.node(ConstructorTag::from(super::tag::OCC), vec![atom])
    }

    /// The binding field of the variable `var` over `body`.
    ///
    /// # Specification
    /// trivial.
    fn lam(
        &mut self,
        var: StringLiteral,
        body: ValueId,
    ) -> ValueId
    {
        let end = self.end();
        let chain = self.node(ConstructorTag::from(super::tag::ARG), vec![body, end]);
        let var = self.text(var);
        self.node(ConstructorTag::from(super::tag::BIND), vec![var, chain])
    }

    /// The variable `var`, named inside a binding field of it.
    ///
    /// # Specification
    /// trivial.
    fn bvar(
        &mut self,
        var: StringLiteral,
    ) -> ValueId
    {
        let var = self.text(var);
        self.node(ConstructorTag::from(super::tag::BVAR), vec![var])
    }

    /// The presentation whose rule chain is `members`, each a tag and its
    /// fields before the rest, ended by `End`.
    ///
    /// # Specification
    /// trivial.
    fn presents(
        &mut self,
        members: Vec<(ConstructorTag, Vec<ValueId>)>,
    ) -> ValueId
    {
        let (sorts, operations) = (self.end(), self.end());
        self.presenting(sorts, operations, members)
    }

    /// The presentation over the sort chain `sorts` and the operation chain
    /// `operations` whose rule chain is `members`, as [`Self::presents`].
    ///
    /// # Specification
    /// trivial.
    fn presenting(
        &mut self,
        sorts: ValueId,
        operations: ValueId,
        members: Vec<(ConstructorTag, Vec<ValueId>)>,
    ) -> ValueId
    {
        let mut chain = self.end();
        for (tag, mut fields) in members.into_iter().rev() {
            fields.push(chain);
            chain = self.node(tag, fields);
        }
        self.node(ConstructorTag::from(super::tag::PRESENTS), vec![
            sorts, operations, chain,
        ])
    }

    /// The sort chain declaring the atom sort `Name` and the operation chain
    /// declaring `out`, whose first input port takes a `Name` when `naming`
    /// is [`super::Naming::Named`] and a `Proc` otherwise.
    ///
    /// # Specification
    /// trivial.
    fn channels(
        &mut self,
        naming: super::Naming,
    ) -> (ValueId, ValueId)
    {
        let literal = |text: &str| StringLiteral::new(String::from(text));
        let tag = ConstructorTag::from;
        let [name, process, out, c, p] =
            ["Name", "Proc", "out", "c", "p"].map(|text| self.text(literal(text)));
        let end = self.end();
        let ordinary = self.node(tag(super::tag::SORT), vec![process, end, end]);
        let sorts = self.node(tag(super::tag::ATOM), vec![name, end, ordinary]);
        let rest = self.node(tag(super::tag::PORT), vec![p, process, end, end]);
        let channel = match naming {
            super::Naming::Named => name,
            super::Naming::Unnamed => process,
        };
        let inputs = self.node(tag(super::tag::PORT), vec![c, channel, end, rest]);
        let operations = self.node(tag(super::tag::OPER), vec![out, inputs, end, end]);
        (sorts, operations)
    }

    /// The sort chain declaring the representable sort `V` and the sort `C`,
    /// and the operation chain declaring `ret : (a : unit) --> C` and
    /// `ext : (m : C, k : pi+ (x : V) . C) --> C`.
    ///
    /// # Specification
    /// trivial.
    fn monad(
        &mut self,
        unit: StringLiteral,
    ) -> (ValueId, ValueId)
    {
        let literal = |text: &str| StringLiteral::new(String::from(text));
        let tag = ConstructorTag::from;
        let [
            values,
            computations_name,
            ret,
            ext,
            argument,
            monadic,
            continuation_name,
            bound,
        ] = ["V", "C", "ret", "ext", "a", "m", "k", "x"].map(|text| self.text(literal(text)));
        let unit = self.text(unit);
        let end = self.end();
        let computations = self.node(tag(super::tag::SORT), vec![computations_name, end, end]);
        let sorts = self.node(tag(super::tag::REPRESENTABLE), vec![
            values,
            end,
            computations,
        ]);
        let binder = self.node(tag(super::tag::PORT), vec![bound, values, end, end]);
        let continuation = self.node(tag(super::tag::BOUND), vec![
            continuation_name,
            computations_name,
            end,
            binder,
            end,
        ]);
        let extended = self.node(tag(super::tag::PORT), vec![
            monadic,
            computations_name,
            end,
            continuation,
        ]);
        let returned = self.node(tag(super::tag::PORT), vec![argument, unit, end, end]);
        let extend = self.node(tag(super::tag::OPER), vec![ext, extended, end, end]);
        let operations = self.node(tag(super::tag::OPER), vec![ret, returned, end, extend]);
        (sorts, operations)
    }
}

#[test]
fn a_presentation_value_reads_as_its_oriented_rules()
{
    let tag = ConstructorTag::from;
    let (rule_tag, turned, derived_tag, rank) = (
        tag(super::tag::RULE),
        tag(super::tag::TURNED),
        tag(super::tag::DERIVED),
        tag(super::tag::RANK),
    );
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let mut code = Code::new();
    let (x, y) = (code.var(literal("x")), code.var(literal("y")));
    let e = code.app(literal("e"), &[]);
    let unit = code.app(literal("mul"), &[e, x]);
    let doubled = code.app(literal("mul"), &[e, e]);
    let derived = code.app(literal("mul"), &[y, e]);
    let names =
        ["unitL", "back", "0", "1", "mul", "2", "e", "01"].map(|name| code.text(literal(name)));
    let [unit_name, back, zero, one, mul, two, e_name, padded] = names;
    let rule_member = (rule_tag, vec![unit_name, unit, x]);
    let turned_member = (turned, vec![back, e, doubled]);
    let derived_member = (derived_tag, vec![zero, one, zero, derived, y]);
    let (mul_rank, e_rank) = ((rank, vec![mul, two]), (rank, vec![e_name, one]));
    let presentation = code.presents(vec![
        rule_member.clone(),
        turned_member,
        derived_member.clone(),
        mul_rank.clone(),
        e_rank,
    ]);
    let read = TheoryRules::read(&code.arena, presentation).expect("the chain reads");
    assert_eq!(read.symbols(), [operation!(2, 2), operation!(1, 0)]);
    assert_eq!(read.rules(), [
        rule(&[s!(0), s!(1), v!(0)], &[v!(0)]),
        rule(&[s!(0), s!(1), s!(1)], &[s!(1)]),
        rule(&[s!(0), v!(0), s!(1)], &[v!(0)]),
    ]);
    assert_eq!(read.peaks(), [CriticalPeak {
        outer: RuleIndex::from(0_usize),
        position: SidePosition::from(1_usize),
        inner: RuleIndex::from(0_usize),
    }]);
    let unreadable = |rule: usize| {
        Err(TheoryRuleRefusal {
            rule: RuleIndex::from(rule),
            fault: TheoryRuleFault::Unreadable,
        })
    };
    let rank_first = code.presents(vec![mul_rank.clone(), rule_member.clone()]);
    assert_eq!(
        TheoryRules::read(&code.arena, rank_first),
        unreadable(0),
        "a rank before a rule"
    );
    let derived_first = code.presents(vec![derived_member, rule_member.clone()]);
    assert_eq!(
        TheoryRules::read(&code.arena, derived_first),
        unreadable(1),
        "a written rule after a derived one"
    );
    let padded_rank = code.presents(vec![rule_member.clone(), (rank, vec![mul, padded])]);
    assert_eq!(
        TheoryRules::read(&code.arena, padded_rank),
        unreadable(1),
        "a padded numeral"
    );
    let ranked_twice = code.presents(vec![rule_member, mul_rank.clone(), mul_rank]);
    assert_eq!(
        TheoryRules::read(&code.arena, ranked_twice),
        unreadable(1),
        "a second rank for one name"
    );
}

#[test]
fn an_abstraction_reads_as_one_symbol_whatever_its_atom()
{
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let mut code = Code::new();
    let nil = code.app(literal("nil"), &[]);
    let stop = code.app(literal("stop"), &[]);
    let (over_a, over_b) = (code.abs(literal("a"), nil), code.abs(literal("b"), nil));
    let (left_a, left_b) = (
        code.app(literal("nu"), &[over_a]),
        code.app(literal("nu"), &[over_b]),
    );
    let [gc, halt] = ["gc", "halt"].map(|name| code.text(literal(name)));
    let rule_tag = ConstructorTag::from(super::tag::RULE);
    let presentation = code.presents(vec![
        (rule_tag, vec![gc, left_a, nil]),
        (rule_tag, vec![halt, left_b, stop]),
    ]);
    let read = TheoryRules::read(&code.arena, presentation).expect("the chain reads");
    assert_eq!(
        read.rules(),
        [
            rule(&[s!(0), s!(1), s!(2)], &[s!(2)]),
            rule(&[s!(0), s!(1), s!(2)], &[s!(3)]),
        ],
        "`bind a .` and `bind b .` are one symbol, so the two left sides are one"
    );
    assert_eq!(
        read.symbols().get(1),
        Some(&(SymbolKind::Abstraction, FieldCount::from(1_usize))),
        "an abstraction is a symbol of one field, its body"
    );
}

#[test]
fn a_freshness_condition_reads_after_its_written_rule()
{
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let mut code = Code::new();
    let (p, q) = (code.var(literal("p")), code.var(literal("q")));
    let over = code.abs(literal("a"), p);
    let restricted = code.app(literal("nu"), &[over]);
    let left = code.app(literal("par"), &[restricted, q]);
    let joined = code.app(literal("par"), &[p, q]);
    let enclosed = code.abs(literal("a"), joined);
    let right = code.app(literal("nu"), &[enclosed]);
    let [scope, a, q_name] = ["scope", "a", "q"].map(|name| code.text(literal(name)));
    let (rule_tag, fresh_tag) = (
        ConstructorTag::from(super::tag::RULE),
        ConstructorTag::from(super::tag::FRESH),
    );
    let unconditioned = code.presents(vec![(rule_tag, vec![scope, left, right])]);
    let conditioned = code.presents(vec![
        (rule_tag, vec![scope, left, right]),
        (fresh_tag, vec![a, q_name]),
    ]);
    assert_eq!(
        TheoryRules::read(&code.arena, conditioned).map(|read| read.rules().to_vec()),
        TheoryRules::read(&code.arena, unconditioned).map(|read| read.rules().to_vec()),
        "a condition holds of every instance while no term names an atom"
    );
    let fresh_first = code.presents(vec![
        (fresh_tag, vec![a, q_name]),
        (rule_tag, vec![scope, left, right]),
    ]);
    assert_eq!(
        TheoryRules::read(&code.arena, fresh_first),
        Err(TheoryRuleRefusal {
            rule: RuleIndex::from(0_usize),
            fault: TheoryRuleFault::Unreadable,
        }),
        "a condition stands after the rule it is stated on"
    );
}

#[test]
fn an_occurrence_counts_to_its_abstraction()
{
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let rule_tag = ConstructorTag::from(super::tag::RULE);
    let mut code = Code::new();
    let nil = code.app(literal("nil"), &[]);
    let stop = code.app(literal("stop"), &[]);
    let [unheard, deaf, outer, inner, leak] =
        ["unheard", "deaf", "outer", "inner", "leak"].map(|name| code.text(literal(name)));
    let sends = |code: &mut Code, channel: &str| {
        let named = code.occ(literal(channel));
        code.app(literal("out"), &[named, nil])
    };
    let restricted = |code: &mut Code, atom: &str, body: ValueId| {
        let over = code.abs(literal(atom), body);
        code.app(literal("nu"), &[over])
    };
    let (sorts, operations) = code.channels(super::Naming::Named);
    let on_a = sends(&mut code, "a");
    let on_b = sends(&mut code, "b");
    let left_a = restricted(&mut code, "a", on_a);
    let left_b = restricted(&mut code, "b", on_b);
    let renamed = code.presenting(sorts, operations, vec![
        (rule_tag, vec![unheard, left_a, nil]),
        (rule_tag, vec![deaf, left_b, stop]),
    ]);
    let read = TheoryRules::read(&code.arena, renamed).expect("the chain reads");
    assert_eq!(
        read.rules(),
        [
            rule(&[s!(0), s!(1), s!(2), s!(3), s!(4)], &[s!(4)]),
            rule(&[s!(0), s!(1), s!(2), s!(3), s!(4)], &[s!(5)]),
        ],
        "`out(a, …)` under `bind a .` and `out(b, …)` under `bind b .` are one term"
    );
    assert_eq!(
        read.symbols().get(3),
        Some(&(
            SymbolKind::Occurrence(BinderDistance::from(0_usize)),
            FieldCount::from(0_usize)
        )),
        "an occurrence is a constant, counted to its own abstraction"
    );
    let under_b = restricted(&mut code, "b", on_a);
    let skipping = restricted(&mut code, "a", under_b);
    let shadowed_inner = restricted(&mut code, "a", on_a);
    let shadowing = restricted(&mut code, "a", shadowed_inner);
    let nested = code.presenting(sorts, operations, vec![
        (rule_tag, vec![outer, skipping, nil]),
        (rule_tag, vec![inner, shadowing, nil]),
    ]);
    let read = TheoryRules::read(&code.arena, nested).expect("the chain reads");
    assert_eq!(
        read.rules(),
        [
            rule(&[s!(0), s!(1), s!(0), s!(1), s!(2), s!(3), s!(4)], &[s!(4)]),
            rule(&[s!(0), s!(1), s!(0), s!(1), s!(2), s!(5), s!(4)], &[s!(4)]),
        ],
        "`a` past `bind b .` counts one abstraction, `a` shadowed by `bind a .` none"
    );
    let free = code.presenting(sorts, operations, vec![(rule_tag, vec![leak, on_a, nil])]);
    assert_eq!(
        TheoryRules::read(&code.arena, free),
        Err(TheoryRuleRefusal {
            rule: RuleIndex::from(0_usize),
            fault: TheoryRuleFault::Unreadable,
        }),
        "an occurrence no abstraction binds"
    );
    let p = code.var(literal("p"));
    let hiding = restricted(&mut code, "a", p);
    let conditioned = |code: &mut Code, naming: super::Naming| {
        let (sorts, operations) = code.channels(naming);
        let presentation = code.presenting(sorts, operations, vec![
            (rule_tag, vec![unheard, left_a, nil]),
            (rule_tag, vec![leak, hiding, p]),
        ]);
        TheoryRules::read(&code.arena, presentation).map(|read| {
            read.rules()
                .iter()
                .map(|rule| rule.conditioned)
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(
        conditioned(&mut code, super::Naming::Named),
        Ok(vec![false, true]),
        "`p` leaves `bind a .` where `out` takes a channel: the rule fires only where its \
         instance names no `a`"
    );
    assert_eq!(
        conditioned(&mut code, super::Naming::Unnamed),
        Ok(vec![false, false]),
        "where no port takes a channel no term names one, and the move holds of every instance"
    );
    let beside = code.app(literal("out"), &[p, hiding]);
    let (sorts, operations) = code.channels(super::Naming::Named);
    let split = code.presenting(sorts, operations, vec![(rule_tag, vec![leak, beside, p])]);
    assert_eq!(
        TheoryRules::read(&code.arena, split),
        Err(TheoryRuleRefusal {
            rule: RuleIndex::from(0_usize),
            fault: TheoryRuleFault::UndecidedCondition,
        }),
        "`p` matched beside `bind a .` and under it compares instances up to the atoms they name"
    );
}

#[test]
fn a_variables_atoms_are_read_off_its_abstractions_2448()
{
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let (rule_tag, fresh_tag) = (
        ConstructorTag::from(super::tag::RULE),
        ConstructorTag::from(super::tag::FRESH),
    );
    let mut code = Code::new();
    let (p, q) = (code.var(literal("p")), code.var(literal("q")));
    let restricted = |code: &mut Code, atom: &str, body: ValueId| {
        let over = code.abs(literal(atom), body);
        code.app(literal("nu"), &[over])
    };
    let par =
        |code: &mut Code, left: ValueId, right: ValueId| code.app(literal("par"), &[left, right]);
    let hidden = restricted(&mut code, "a", p);
    let scoped = par(&mut code, hidden, q);
    let joined = par(&mut code, p, q);
    let extruded = restricted(&mut code, "a", joined);
    let tagged = code.app(literal("tag"), &[p]);
    let kept = restricted(&mut code, "a", tagged);
    let inner = restricted(&mut code, "b", p);
    let swapped_from = restricted(&mut code, "a", inner);
    let inner = restricted(&mut code, "a", p);
    let swapped_to = restricted(&mut code, "b", inner);
    let [scope, gc, keep, swap, a, p_name, q_name] =
        ["scope", "gc", "keep", "swap", "a", "p", "q"].map(|name| code.text(literal(name)));
    let (sorts, operations) = code.channels(super::Naming::Named);
    let presentation = code.presenting(sorts, operations, vec![
        (rule_tag, vec![scope, scoped, extruded]),
        (fresh_tag, vec![a, q_name]),
        (rule_tag, vec![gc, hidden, p]),
        (fresh_tag, vec![a, p_name]),
        (rule_tag, vec![keep, kept, hidden]),
        (rule_tag, vec![swap, swapped_from, swapped_to]),
    ]);
    let read = TheoryRules::read(&code.arena, presentation).expect("the chain reads");
    let holes = |rule: usize, occurrences: usize| {
        read.rules().get(rule).map(|rule| {
            (0 .. occurrences)
                .map(|at| rule.holes(super::Occurrence(at)).to_vec())
                .collect::<Vec<_>>()
        })
    };
    let at = |distances: &[usize]| {
        distances
            .iter()
            .map(|&distance| BinderDistance::from(distance))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        holes(0, 4),
        Some(vec![at(&[0]), at(&[]), at(&[0]), at(&[])]),
        "scope extrusion keeps `p` naming its restriction's atom and moves `q`, fresh for it, \
         in naming none"
    );
    assert_eq!(
        holes(1, 2),
        Some(vec![at(&[]), at(&[])]),
        "garbage collection's `p`, fresh for `a`, names no atom"
    );
    assert_eq!(
        holes(2, 2),
        Some(vec![at(&[0]), at(&[0])]),
        "a law under one abstraction on both sides names its atom on both"
    );
    assert_eq!(
        holes(3, 2),
        Some(vec![at(&[1, 0]), at(&[0, 1])]),
        "swapping two abstractions swaps the distances the variable names them at"
    );
}

#[test]
fn conditioned_rules_join_under_the_condition_their_overlap_composes_2448()
{
    let literal = |text: &str| StringLiteral::new(String::from(text));
    let tag = ConstructorTag::from;
    let (rule_tag, fresh_tag, rank) = (
        tag(super::tag::RULE),
        tag(super::tag::FRESH),
        tag(super::tag::RANK),
    );
    let mut code = Code::new();
    let (p, q) = (code.var(literal("p")), code.var(literal("q")));
    let nil = code.app(literal("nil"), &[]);
    let hidden = code.abs(literal("a"), p);
    let restricted = code.app(literal("nu"), &[hidden]);
    let scoped = code.app(literal("par"), &[restricted, q]);
    let joined = code.app(literal("par"), &[p, q]);
    let enclosed = code.abs(literal("a"), joined);
    let extruded = code.app(literal("nu"), &[enclosed]);
    let nothing = code.abs(literal("a"), nil);
    let empty = code.app(literal("nu"), &[nothing]);
    let named = code.occ(literal("a"));
    let sends = code.app(literal("out"), &[named, nil]);
    let sending = code.abs(literal("a"), sends);
    let unheard = code.app(literal("nu"), &[sending]);
    let [
        scope,
        gc,
        drop,
        quiet,
        a,
        p_name,
        q_name,
        par,
        nu,
        out,
        one,
        two,
    ] = [
        "scope", "gc", "drop", "quiet", "a", "p", "q", "par", "nu", "out", "1", "2",
    ]
    .map(|name| code.text(literal(name)));
    let extrusion = [
        (rule_tag, vec![scope, scoped, extruded]),
        (fresh_tag, vec![a, q_name]),
    ];
    let collection = [
        (rule_tag, vec![gc, restricted, p]),
        (fresh_tag, vec![a, p_name]),
    ];
    let dropping = [(rule_tag, vec![drop, empty, nil])];
    let silenced = [(rule_tag, vec![quiet, unheard, nil])];
    let ranks = [
        (rank, vec![par, two]),
        (rank, vec![nu, one]),
        (rank, vec![out, one]),
    ];
    let decided = |code: &mut Code,
                   naming: super::Naming,
                   rules: &[&[(ConstructorTag, Vec<ValueId>)]]|
     -> Result<(), TheoryRuleRefusal> {
        let (sorts, operations) = code.channels(naming);
        let members = rules
            .iter()
            .flat_map(|rule| rule.iter().cloned())
            .chain(ranks.iter().cloned())
            .collect();
        let presentation = code.presenting(sorts, operations, members);
        TheoryRules::read(&code.arena, presentation)?.decide(&mut fuel())
    };
    for naming in [super::Naming::Named, super::Naming::Unnamed] {
        assert_eq!(
            decided(&mut code, naming, &[&extrusion]),
            Ok(()),
            "scope extrusion converges alone"
        );
        assert_eq!(
            decided(&mut code, naming, &[&collection]),
            Ok(()),
            "garbage collection converges alone"
        );
        assert_eq!(
            decided(&mut code, naming, &[&extrusion, &collection]),
            Ok(()),
            "collection overlaps extrusion where the restricted process names no `a`, and \
             there the two join"
        );
    }
    assert_eq!(
        decided(&mut code, super::Naming::Named, &[&extrusion, &dropping]),
        refused!(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "a restriction of nothing extruded keeps its restriction, which dropping it does not \
         rewrite"
    );
    assert_eq!(
        decided(&mut code, super::Naming::Named, &[&collection, &silenced]),
        Ok(()),
        "collection fires only where the restricted process names no `a`, and a process \
         sending on `a` names it: the overlap is vacuous and owes no join"
    );
}

/// #2448: rows are sets, ordered by the rows they describe, and two rows meet
/// at their unifier.
#[test]
fn rows_compose_as_their_unifier_2448()
{
    use core::cmp::Ordering;

    use super::row::RowExtent;
    use super::row::RowLabel;
    use super::row::RuleRow;

    let [state, console, file] = [0_u32, 1, 2].map(RowLabel::from);
    let open = |labels: &[RowLabel]| RuleRow::new(labels.iter().copied(), RowExtent::AtLeast);
    let closed = |labels: &[RowLabel]| RuleRow::new(labels.iter().copied(), RowExtent::Exactly);
    assert_eq!(
        closed(&[console, state, state]),
        closed(&[state, console]),
        "a row names each theory once, in no order"
    );
    assert_eq!(
        RuleRow::default(),
        open(&[]),
        "an unconditioned rule fires in every row"
    );
    assert_eq!(
        open(&[state]).meet(&open(&[console])),
        Some(open(&[state, console])),
        "two open rows meet at the union of their theories"
    );
    assert_eq!(
        open(&[state]).meet(&closed(&[state, console])),
        Some(closed(&[state, console])),
        "an open row meets a closed row holding its theories at the closed row"
    );
    assert_eq!(
        closed(&[state, console]).meet(&open(&[file])),
        None,
        "a closed row without the open row's theory shares no row with it"
    );
    assert_eq!(
        closed(&[state]).meet(&closed(&[console])),
        None,
        "two distinct closed rows share no row"
    );
    assert_eq!(
        closed(&[state]).meet(&closed(&[state])),
        Some(closed(&[state]))
    );
    assert_eq!(
        [
            closed(&[state, console]).partial_cmp(&open(&[state])),
            open(&[state, console]).partial_cmp(&open(&[state])),
            open(&[state]).partial_cmp(&RuleRow::default()),
            open(&[state]).partial_cmp(&closed(&[state])),
            closed(&[state]).partial_cmp(&closed(&[console])),
            open(&[state]).partial_cmp(&open(&[console])),
        ],
        [
            Some(Ordering::Less),
            Some(Ordering::Less),
            Some(Ordering::Less),
            Some(Ordering::Greater),
            None,
            None,
        ],
        "a row lies below an open row when it holds that row's theories, and below a closed \
         row only when it is that row"
    );
}

/// #2448: rows under their meet are a semilattice, with no meet absorbing,
/// so conditions composed along a chain of overlaps compose alike in any
/// grouping: over every row three theories write, the meet commutes, is
/// idempotent and associates, and a row lies below two rows exactly when it
/// lies below their meet.
#[test]
fn rows_meet_as_a_semilattice_2448()
{
    use super::row::RowExtent;
    use super::row::RowLabel;
    use super::row::RuleRow;

    let rows: Vec<RuleRow> = (0_u32 .. 8)
        .flat_map(|set| {
            let labels: Vec<RowLabel> = (0_u32 .. 3)
                .filter(|label| set & (1 << label) != 0)
                .map(RowLabel::from)
                .collect();
            [RowExtent::AtLeast, RowExtent::Exactly]
                .map(|extent| RuleRow::new(labels.iter().copied(), extent))
        })
        .collect();
    for a in &rows {
        assert_eq!(a.meet(a).as_ref(), Some(a), "{a:?} meets itself at itself");
        for b in &rows {
            assert_eq!(
                a.meet(b),
                b.meet(a),
                "{a:?} and {b:?} meet alike either way"
            );
            for c in &rows {
                assert_eq!(
                    a.meet(b).and_then(|ab| ab.meet(c)),
                    b.meet(c).and_then(|bc| a.meet(&bc)),
                    "{a:?}, {b:?} and {c:?} meet alike in either grouping"
                );
                assert_eq!(
                    c <= a && c <= b,
                    a.meet(b).is_some_and(|met| *c <= met),
                    "{c:?} lies below {a:?} and {b:?} exactly when below their meet"
                );
            }
        }
    }
}

/// #2448: rules stated under rows join where the row their overlap composes
/// holds, under the rules that fire in it, and an overlap of rows that share
/// no row owes no join.
#[test]
fn rules_under_rows_join_under_the_row_their_overlap_composes_2448()
{
    use super::row::RowExtent;
    use super::row::RowLabel;
    use super::row::RuleRow;

    let literal = |text: &str| StringLiteral::new(String::from(text));
    let tag = ConstructorTag::from;
    let (rule_tag, under, open, fresh, rank) = (
        tag(super::tag::RULE),
        tag(super::tag::UNDER),
        tag(super::tag::OPEN),
        tag(super::tag::FRESH),
        tag(super::tag::RANK),
    );
    let mut code = Code::new();
    let variable = code.var(literal("x"));
    let gx = code.app(literal("g"), &[variable]);
    let fgx = code.app(literal("f"), &[gx]);
    let hx = code.app(literal("h"), &[variable]);
    let [first, second, third, state, console, file, atom] =
        ["r1", "r2", "r3", "State", "Console", "File", "a"].map(|name| code.text(literal(name)));
    let [f_name, g_name, h_name, one, two] =
        ["f", "g", "h", "1", "2"].map(|name| code.text(literal(name)));
    let ranks = [
        (rank, vec![f_name, two]),
        (rank, vec![g_name, one]),
        (rank, vec![h_name, one]),
    ];
    let stated = |name: ValueId,
                  sides: [ValueId; 2],
                  theories: &[ValueId],
                  extent: RowExtent|
     -> Vec<(ConstructorTag, Vec<ValueId>)> {
        let [left, right] = sides;
        let mut members = vec![(rule_tag, vec![name, left, right])];
        members.extend(theories.iter().map(|&theory| (under, vec![theory])));
        if extent == RowExtent::AtLeast {
            members.push((open, Vec::new()));
        }
        members
    };
    let decided = |code: &mut Code,
                   rules: &[&[(ConstructorTag, Vec<ValueId>)]]|
     -> Result<(), TheoryRuleRefusal> {
        let mut members = rules.concat();
        members.extend(ranks.iter().cloned());
        let presentation = code.presents(members);
        TheoryRules::read(&code.arena, presentation)?.decide(&mut fuel())
    };
    let r1 = stated(first, [fgx, hx], &[state], RowExtent::AtLeast);
    let r2 = stated(second, [fgx, variable], &[console], RowExtent::AtLeast);
    let r3 = stated(third, [hx, variable], &[state, console], RowExtent::AtLeast);
    let rowed = code.presents([r1.as_slice(), r3.as_slice()].concat());
    let read = TheoryRules::read(&code.arena, rowed).expect("the rows read");
    assert_eq!(
        read.rules()
            .iter()
            .map(|rule| rule.row.clone())
            .collect::<Vec<_>>(),
        [
            RuleRow::new([RowLabel::from(0_u32)], RowExtent::AtLeast),
            RuleRow::new([0_u32, 1].map(RowLabel::from), RowExtent::AtLeast),
        ],
        "each theory a row names is numbered by its first naming"
    );
    assert_eq!(
        decided(&mut code, &[&r1, &r2, &r3]),
        Ok(()),
        "the two rules on `f(g(x))` overlap in rows holding `State` and `Console`, and there \
         `h(x)` rewrites to `x`"
    );
    assert_eq!(
        decided(&mut code, &[&r1, &r2]),
        refused!(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "without the third rule `h(x)` and `x` stay apart"
    );
    let r3_more = stated(
        third,
        [hx, variable],
        &[state, console, file],
        RowExtent::AtLeast,
    );
    assert_eq!(
        decided(&mut code, &[&r1, &r2, &r3_more]),
        refused!(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "a rule needing `File` too does not fire in every row the overlap composes"
    );
    let r1_closed = stated(first, [fgx, hx], &[state], RowExtent::Exactly);
    let r2_closed = stated(second, [fgx, variable], &[console], RowExtent::Exactly);
    assert_eq!(
        decided(&mut code, &[&r1_closed, &r2_closed]),
        Ok(()),
        "a row holding exactly `State` is never one holding exactly `Console`: the overlap is \
         vacuous"
    );
    let malformed: [&[(ConstructorTag, Vec<ValueId>)]; 3] = [
        &[(open, Vec::new())],
        &[(rule_tag, vec![first, fgx, hx]), (open, Vec::new())],
        &[
            (rule_tag, vec![first, fgx, hx]),
            (under, vec![state]),
            (fresh, vec![atom, first]),
        ],
    ];
    for (members, case) in malformed.into_iter().zip([
        "an open tail before any rule",
        "an open tail after no theory",
        "a freshness condition after the row",
    ]) {
        let presentation = code.presents(members.to_vec());
        assert!(
            matches!(
                TheoryRules::read(&code.arena, presentation),
                Err(TheoryRuleRefusal {
                    fault: TheoryRuleFault::Unreadable,
                    ..
                })
            ),
            "{case}"
        );
    }
}
