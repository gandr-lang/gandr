use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Literal;
use gandr_kernel_term::PRESENTATION_CODE;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::TheoryRuleFault;
use gandr_kernel_term::TheoryRuleRefusal;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use crate::env::Environment;
use crate::error::KernelError;

/// The presentation.
const PRESENTS: usize = 0;
/// The end of a chain.
const END: usize = 1;
/// A rule as written.
const RULE: usize = 5;
/// A variable.
const VAR: usize = 6;
/// An operation application.
const APP: usize = 7;
/// An argument.
const ARG: usize = 10;
/// A derived rule.
const DERIVED: usize = 17;
/// A rank.
const RANK: usize = 18;

/// One node of a term in pre-order.
#[derive(Clone, Copy)]
enum Token
{
    /// The variable of this name.
    Var(&'static str),
    /// The operation of this name over the next this many subterms.
    App(&'static str, usize),
}

/// A member of a rule chain, each term in pre-order.
#[derive(Clone, Copy)]
enum Member
{
    /// A written rule.
    Rule(&'static [Token], &'static [Token]),
    /// A derived rule and its peak's three numerals.
    Derived([&'static str; 3], &'static [Token], &'static [Token]),
    /// An operation's rank.
    Rank(&'static str, &'static str),
}

/// The string literal spelling `text`.
///
/// # Specification
/// trivial.
fn literal<T>(text: T) -> StringLiteral
where
    T: AsRef<str>,
{
    StringLiteral::new(String::from(text.as_ref()))
}

/// Values of the code at position zero, minted into an arena.
struct Minting<'arena>
{
    /// The arena.
    arena: &'arena mut TermArena,
    /// The code's type.
    code: ValueTypeId,
}

impl Minting<'_>
{
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
        self.arena.value_constructor(self.code, tag, fields)
    }

    /// The value of the term `tokens` spell in pre-order.
    ///
    /// # Specification
    /// trivial.
    fn term(
        &mut self,
        tokens: &[Token],
    ) -> ValueId
    {
        let mut built: Vec<ValueId> = Vec::new();
        for &token in tokens.iter().rev() {
            let value = match token {
                Token::Var(name) => {
                    let name = self.text(literal(name));
                    self.node(ConstructorTag::from(VAR), vec![name])
                },
                Token::App(name, arity) => {
                    let mut chain = self.node(ConstructorTag::from(END), vec![]);
                    let first = built.len().saturating_sub(arity);
                    for &argument in built.get(first ..).unwrap_or(&[]) {
                        chain = self.node(ConstructorTag::from(ARG), vec![argument, chain]);
                    }
                    built.truncate(first);
                    let name = self.text(literal(name));
                    self.node(ConstructorTag::from(APP), vec![name, chain])
                },
            };
            built.push(value);
        }
        built.pop().expect("the tokens spell one term")
    }

    /// The presentation of no sort and no operation whose rule chain is
    /// `members`.
    ///
    /// # Specification
    /// trivial.
    fn presents(
        &mut self,
        members: &[Member],
    ) -> ValueId
    {
        let mut chain = self.node(ConstructorTag::from(END), vec![]);
        for &member in members.iter().rev() {
            chain = match member {
                Member::Rule(left, right) => {
                    let name = self.text(literal("r"));
                    let (left, right) = (self.term(left), self.term(right));
                    self.node(ConstructorTag::from(RULE), vec![name, left, right, chain])
                },
                Member::Derived(peak, left, right) => {
                    let [outer, position, inner] = peak.map(|numeral| self.text(literal(numeral)));
                    let (left, right) = (self.term(left), self.term(right));
                    self.node(ConstructorTag::from(DERIVED), vec![
                        outer, position, inner, left, right, chain,
                    ])
                },
                Member::Rank(name, rank) => {
                    let name = self.text(literal(name));
                    let rank = self.text(literal(rank));
                    self.node(ConstructorTag::from(RANK), vec![name, rank, chain])
                },
            };
        }
        let sorts = self.node(ConstructorTag::from(END), vec![]);
        let operations = self.node(ConstructorTag::from(END), vec![]);
        self.node(ConstructorTag::from(PRESENTS), vec![
            sorts, operations, chain,
        ])
    }
}

/// Admit the presentation code at position zero.
///
/// # Specification
/// trivial.
fn admit_code(environment: &mut Environment)
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let constructors: Vec<Vec<ValueTypeId>> = PRESENTATION_CODE
        .iter()
        .map(|&(strings, recursions)| {
            let mut fields = vec![string; strings];
            fields.extend(core::iter::repeat_n(code, recursions));
            fields
        })
        .collect();
    let declaration = staging.data(LevelSignature::monomorphic(), vec![], constructors, kind);
    let _code = environment.add_decl(declaration).expect("the code admits");
}

/// Admit a definition of the code whose body presents `members`.
///
/// # Specification
/// trivial.
fn admit(
    environment: &mut Environment,
    members: &[Member],
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let code = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let body = Minting { arena, code }.presents(members);
    let declaration = staging.def(LevelSignature::monomorphic(), code, body);
    environment.add_decl(declaration).map(|_admitted| ())
}

#[test]
fn a_presentation_is_admitted_only_when_its_rules_converge()
{
    use Token::App;
    use Token::Var;
    /// `mul(e(), x)`.
    const UNIT_CALL: &[Token] = &[App("mul", 2), App("e", 0), Var("x")];
    /// `e()`.
    const E: &[Token] = &[App("e", 0)];
    /// `x`.
    const X: &[Token] = &[Var("x")];
    /// `mul(inv(x), x)`.
    const INVERSE: &[Token] = &[App("mul", 2), App("inv", 1), Var("x"), Var("x")];
    /// `inv(inv(x))`.
    const INVOLUTION: &[Token] = &[App("inv", 1), App("inv", 1), Var("x")];
    /// `mul(y, inv(y))`.
    const RIGHT_INVERSE: &[Token] = &[App("mul", 2), Var("y"), App("inv", 1), Var("y")];
    let refused = |rule: usize, fault| {
        Err(KernelError::PresentationRulesRefused(TheoryRuleRefusal {
            rule: RuleIndex::from(rule),
            fault,
        }))
    };
    let mut environment = Environment::new();
    admit_code(&mut environment);
    let unit = Member::Rule(UNIT_CALL, X);
    assert_eq!(admit(&mut environment, &[unit]), Ok(()));
    assert_eq!(
        admit(&mut environment, &[unit, Member::Rule(UNIT_CALL, E)]),
        refused(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "the forged law rewrites the unit's call apart"
    );
    let (inverse, involution) = (Member::Rule(INVERSE, E), Member::Rule(INVOLUTION, X));
    let (mul, inv) = (Member::Rank("mul", "1"), Member::Rank("inv", "1"));
    assert_eq!(
        admit(&mut environment, &[inverse, involution, mul, inv]),
        refused(0, TheoryRuleFault::Diverges(RuleIndex::from(1_usize))),
        "the inverse law alone leaves its overlap with the involution apart"
    );
    let completed = |peak| {
        [
            inverse,
            involution,
            Member::Derived(peak, RIGHT_INVERSE, E),
            mul,
            inv,
        ]
    };
    assert_eq!(
        admit(&mut environment, &completed(["0", "1", "1"])),
        Ok(()),
        "the derived rule replays its peak and completes the rules"
    );
    assert_eq!(
        admit(&mut environment, &completed(["1", "1", "1"])),
        refused(2, TheoryRuleFault::NoPeak),
        "a peak the rule does not join"
    );
}
