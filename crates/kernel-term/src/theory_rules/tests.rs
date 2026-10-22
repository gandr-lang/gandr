use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use super::CriticalPeak;
use super::OperationRank;
use super::PRESENTATION_CODE;
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
    assert_eq!(
        written.peak_of(&right_inverse, &mut fuel()),
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
    assert_eq!(written.peak_of(&unreached, &mut fuel()), Ok(None));
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
        decided(vec![zeta, at_zero]),
        refused!(0, TheoryRuleFault::Overlaps(RuleIndex::from(1_usize))),
        "a second-order rule takes part in no critical pair, even one that would join"
    );
    assert_eq!(
        decided(vec![rule(&[s!(0), v!(0), i!(0, 0)], &[v!(0)])]),
        refused!(0, TheoryRuleFault::Malformed),
        "an instantiation on a left side"
    );
    assert_eq!(
        decided(vec![rule(&[s!(0), v!(0), v!(1)], &[i!(2, 1), v!(0)])]),
        refused!(0, TheoryRuleFault::Unbound),
        "an instantiation of a variable the left side does not bind"
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
        let mut chain = self.end();
        for (tag, mut fields) in members.into_iter().rev() {
            fields.push(chain);
            chain = self.node(tag, fields);
        }
        let (sorts, operations) = (self.end(), self.end());
        self.node(ConstructorTag::from(super::tag::PRESENTS), vec![
            sorts, operations, chain,
        ])
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
        Some(&(SymbolKind::Constructor, FieldCount::from(1_usize))),
        "an abstraction is a constructor of one field"
    );
}
