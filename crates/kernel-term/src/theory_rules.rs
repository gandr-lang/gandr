//! The rules of a presentation: the kernel's decision that a `Theory` value's
//! rules, completed by the rules it carries derived, are one convergent
//! rewriting system.
//!
//! A `theory` block's core definition is a value of the presentation code,
//! `Theory`. Its rule chain carries, beside each written rule, what the
//! decision replays rather than searches for: the rule's orientation (`Rule`
//! as written, `Turned` right to left) and the freshness conditions it states
//! (`Fresh`), the rules a completion derived (`Derived`, each naming the
//! critical pair it joins) and each operation's rank (`Rank`).
//! [`TheoryRules::read`] reads the chain and
//! [`TheoryRules::decide`] decides it in four steps:
//!
//! 1. every side is one term, every left side is headed by an operation and
//!    instantiates no variable, its variables numbered by first occurrence, and
//!    every right side names and instantiates only variables its left side
//!    binds;
//! 2. the lexicographic path order over the stated ranks puts every left side
//!    above its right: an operation stands above every operation of a lower
//!    rank and above every constructor and results tuple, and the order is a
//!    simplification order whatever the ranks, so the rules terminate. A
//!    variable a right side instantiates is read at a function type, the order
//!    then the higher-order recursive path order: a left side is above an
//!    instantiation when the variable is one of its arguments and it covers
//!    every argument of the instantiation;
//! 3. each derived rule is, up to its variables' names, the two normal forms
//!    under the rules before it of the critical pair it names, so it is an
//!    equation the rules before it prove;
//! 4. no rule that instantiates a variable overlaps or is overlapped by a rule,
//!    and every other critical pair of the rules joins.
//!
//! By the critical pair lemma and Newman's lemma the rules are then confluent
//! and terminating, and by step 3 they decide exactly the equations the
//! written rules generate. Nothing is searched for: a derived rule the value
//! does not carry, or one whose peak does not replay, leaves its pair to part
//! in step 4 or is refused by name in step 3.
//!
//! The terms are first order but for instantiations. A symbol is an
//! operation application, a constructor application, a results tuple or an
//! atom's abstraction, interned by its kind, its name and its argument count;
//! two symbols are one exactly when all three agree. An abstraction is
//! interned without the atom it names, so its symbol is the canonical
//! re-minting the checker admits it under: a rule that renames the atom is the
//! same rule. The order and matching read it as a constructor of one field.
//! A left side may repeat a variable, so matching compares the subterms a
//! repeated variable binds and the critical pairs come from unification with
//! an occurs check. A rule that instantiates a variable — a second-order rule,
//! `let(u, t) ==> t(u)` — substitutes under a binder no first-order term
//! marks, so it rewrites no term the decision normalizes; the orthogonality
//! step 4 asks of it is what keeps the critical pair lemma in reach for
//! patterns (Mayr and Nipkow).
//!
//! # References
//!
//! - Donald E. Knuth and Peter B. Bendix. "Simple Word Problems in Universal
//!   Algebras." _Computational Problems in Abstract Algebra_, Pergamon, 1970 —
//!   completion and the critical pair lemma.
//! - Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge
//!   University Press, 1998, §§ 4.6, 5.4 and 6.2 — unification, the
//!   lexicographic path order and critical pairs.
//! - Jean-Pierre Jouannaud and Albert Rubio. "The Higher-Order Recursive Path
//!   Ordering." LICS 1999 — the order on instantiations.
//! - Richard Mayr and Tobias Nipkow. "Higher-Order Rewrite Systems and their
//!   Confluence." _Theoretical Computer Science_ 192(1), 1998 — critical pairs
//!   of pattern rewrite systems.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;

use crate::Literal;
use crate::StringLiteral;
use crate::TermArena;
use crate::Value;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;
use crate::base::BaseType;
use crate::presented::Exhausted;
use crate::presented::FieldCount;
use crate::presented::RewriteFuel;
use crate::presented::RuleIndex;
use crate::presented::RuleVariable;
use crate::term::ConstantIndex;
use crate::term::ConstructorTag;

/// The nodes one presentation's decision may scan or copy, at every caller:
/// a bound on a pathological presentation, far above the few million a
/// completed group's forty-one rules spend.
pub const PRESENTATION_FUEL: u64 = 1 << 26;

/// Each constructor of the presentation code, in tag order: its count of
/// string fields, which come first, and its count of recursive fields after
/// them.
pub const PRESENTATION_CODE: [(usize, usize); 26] = [
    (0, 3),
    (0, 0),
    (1, 2),
    (1, 3),
    (2, 2),
    (1, 3),
    (1, 0),
    (1, 1),
    (1, 1),
    (0, 1),
    (0, 2),
    (1, 2),
    (2, 3),
    (2, 2),
    (2, 1),
    (1, 3),
    (1, 3),
    (3, 3),
    (2, 1),
    (1, 3),
    (1, 3),
    (1, 1),
    (1, 2),
    (2, 4),
    (1, 1),
    (2, 1),
];

/// The presentation code's constructor tags this module reads.
mod tag
{
    /// The presentation: its sort, operation and rule chains.
    pub(super) const PRESENTS: usize = 0;
    /// The end of a chain.
    pub(super) const END: usize = 1;
    /// A rule oriented as written.
    pub(super) const RULE: usize = 5;
    /// A variable.
    pub(super) const VAR: usize = 6;
    /// An operation application.
    pub(super) const APP: usize = 7;
    /// A constructor application.
    pub(super) const CON: usize = 8;
    /// A results tuple.
    pub(super) const TUPLE: usize = 9;
    /// An argument and the rest of the arguments.
    pub(super) const ARG: usize = 10;
    /// A rule oriented right to left.
    pub(super) const TURNED: usize = 16;
    /// A derived rule and the critical pair it joins.
    pub(super) const DERIVED: usize = 17;
    /// An operation's rank.
    pub(super) const RANK: usize = 18;
    /// A variable's instantiation.
    pub(super) const INST: usize = 21;
    /// An atom's abstraction over its body.
    pub(super) const ABS: usize = 24;
    /// A freshness condition on the written rule before it.
    pub(super) const FRESH: usize = 25;
}

/// Whether a data declaration's constructor table is the presentation code's.
///
/// The code has one constructor per row of [`PRESENTATION_CODE`], each with
/// that row's string fields and then that row's fields of `own` itself.
///
/// # Specification
/// - ensures: positive exactly when `constructors` has as many entries as
///   [`PRESENTATION_CODE`], and each has the row's count of `String` fields
///   followed by the row's count of fields of the unapplied `own`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the code's own table is recognised, and the same table
///   short one constructor, with a string field read as a recursion, or
///   recurring into another declaration, is not.
/// - witness: `theory_rules::tests::the_presentation_code_is_recognised_by_its_table`
#[spec(ensures: |ret| !bool::from(ret) || constructors.len() == PRESENTATION_CODE.len())]
#[inline]
#[must_use]
pub fn presentation_code(
    arena: &TermArena,
    own: ConstantIndex,
    constructors: &[Vec<ValueTypeId>],
) -> CodeRecognition
{
    let field = |id: ValueTypeId, string: bool| match arena.value_type(id) {
        Some(&ValueType::Base(BaseType::String)) => string,
        Some(&ValueType::Data {
            declaration,
            ref arguments,
        }) => !string && declaration == own && arguments.is_empty(),
        Some(_) | None => false,
    };
    CodeRecognition::from(
        constructors.len() == PRESENTATION_CODE.len()
            && constructors
                .iter()
                .zip(PRESENTATION_CODE)
                .all(|(fields, (strings, recursions))| {
                    fields.len() == strings.saturating_add(recursions)
                        && fields
                            .iter()
                            .enumerate()
                            .all(|(index, &id)| field(id, index < strings))
                }),
    )
}

/// Whether a data declaration is the presentation code.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CodeRecognition(bool);

impl From<bool> for CodeRecognition
{
    /// The recognition `recognised` states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(recognised: bool) -> Self
    {
        Self(recognised)
    }
}

impl From<CodeRecognition> for bool
{
    /// Whether the declaration is the code.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(recognition: CodeRecognition) -> Self
    {
        recognition.0
    }
}

/// One symbol of a presentation's rule terms, by its place in the symbol
/// table.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TheorySymbol(usize);

impl From<usize> for TheorySymbol
{
    /// The symbol at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<TheorySymbol> for usize
{
    /// The symbol's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(symbol: TheorySymbol) -> Self
    {
        symbol.0
    }
}

/// An operation's place in the order: above every operation of a lower rank
/// and beside every operation of its own.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OperationRank(u32);

impl From<u32> for OperationRank
{
    /// The rank `rank`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: u32) -> Self
    {
        Self(rank)
    }
}

impl From<OperationRank> for u32
{
    /// The rank's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: OperationRank) -> Self
    {
        rank.0
    }
}

/// What a symbol applies, as the order reads it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SymbolKind
{
    /// An operation at its rank.
    Operation(OperationRank),
    /// A constructor or a results tuple: below every operation.
    Constructor,
}

/// One node of a rule side, in pre-order: a symbol applied to the next
/// subterms its arity counts, a variable, or a variable instantiated at the
/// next subterms its count names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TheoryNode
{
    /// A symbol of the table.
    Symbol(TheorySymbol),
    /// A variable, numbered by first occurrence on the rule's left side.
    Variable(RuleVariable),
    /// A right side's instantiation of a variable its left side binds at the
    /// next `FieldCount` subterms, one per variable the binding binds.
    Instance(RuleVariable, FieldCount),
}

/// One oriented rule: its left side rewrites to its right.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryRule
{
    /// The left side, in pre-order.
    left: Box<[TheoryNode]>,
    /// The right side, in pre-order.
    right: Box<[TheoryNode]>,
    /// Whether the right side instantiates a variable: a second-order rule,
    /// which rewrites no term the decision normalizes and overlaps no rule.
    instantiates: bool,
}

impl TheoryRule
{
    /// The rule rewriting `left` to `right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        left: Box<[TheoryNode]>,
        right: Box<[TheoryNode]>,
    ) -> Self
    {
        let instantiates = right
            .iter()
            .any(|node| matches!(*node, TheoryNode::Instance(..)));
        Self {
            left,
            right,
            instantiates,
        }
    }

    /// The left side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn left(&self) -> &[TheoryNode]
    {
        &self.left
    }

    /// The right side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn right(&self) -> &[TheoryNode]
    {
        &self.right
    }
}

/// A position in a rule side, by its pre-order index.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SidePosition(usize);

impl From<usize> for SidePosition
{
    /// The position `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<SidePosition> for usize
{
    /// The position's index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: SidePosition) -> Self
    {
        position.0
    }
}

/// The critical pair a derived rule joins: `inner`'s left side unified with
/// the subterm of `outer`'s left side at `position`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CriticalPeak
{
    /// The rule overlapped, rewritten at the overlap's root.
    pub outer: RuleIndex,
    /// The operation position of `outer`'s left side the overlap stands at.
    pub position: SidePosition,
    /// The rule overlapping it, rewritten at `position`.
    pub inner: RuleIndex,
}

/// Why a presentation's rules are refused.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TheoryRuleFault
{
    /// The rule chain is not one the presentation code's grammar writes: a
    /// member out of place, a term position holding no term, or a peak or a
    /// rank not in its one numeral spelling.
    Unreadable,
    /// A side is not one term, the left side is not headed by an operation,
    /// numbers its variables out of order or instantiates a variable.
    Malformed,
    /// The right side names a variable the left side does not bind.
    Unbound,
    /// The path order over the stated ranks does not put the left side above
    /// the right.
    Unoriented,
    /// The derived rule is not the two normal forms of the critical pair it
    /// names under the rules before it.
    NoPeak,
    /// The rule, overlapped by the one named, rewrites one term to two normal
    /// forms.
    Diverges(RuleIndex),
    /// The rule, overlapped by the one named, is one of two overlapping rules
    /// at least one of which instantiates a variable: a second-order rule takes
    /// part in no critical pair.
    Overlaps(RuleIndex),
    /// The decision's fuel ran out at the rule.
    Exhausted,
}

/// The first rule a presentation's rules are refused at, and why. Rules are
/// numbered written first, then derived, each in chain order.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TheoryRuleRefusal
{
    /// The rule.
    pub rule: RuleIndex,
    /// Its fault.
    pub fault: TheoryRuleFault,
}

/// A presentation's rules as the decision reads them: the symbol table, the
/// written rules oriented, and the derived rules with their peaks.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TheoryRules
{
    /// Each symbol's kind and arity, by its position.
    symbols: Vec<(SymbolKind, FieldCount)>,
    /// The written rules, then the derived ones.
    rules: Vec<TheoryRule>,
    /// One peak per derived rule, in order: the last `peaks.len()` rules.
    peaks: Vec<CriticalPeak>,
}

impl TheoryRules
{
    /// The written rules `written` over `symbols`, with no derived rule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        symbols: Vec<(SymbolKind, FieldCount)>,
        written: Vec<TheoryRule>,
    ) -> Self
    {
        Self {
            symbols,
            rules: written,
            peaks: Vec::new(),
        }
    }

    /// Append `rule`, derived to join `peak`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn derive(
        &mut self,
        rule: TheoryRule,
        peak: CriticalPeak,
    )
    {
        self.rules.push(rule);
        self.peaks.push(peak);
    }

    /// The symbol table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn symbols(&self) -> &[(SymbolKind, FieldCount)]
    {
        &self.symbols
    }

    /// The rules, written first, then derived.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[TheoryRule]
    {
        &self.rules
    }

    /// The peak of each derived rule, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn peaks(&self) -> &[CriticalPeak]
    {
        &self.peaks
    }

    /// The rules a value of the presentation code carries.
    ///
    /// # Specification
    /// - requires: nothing — the value may be arbitrary producer bytes.
    /// - ensures: the root is `Presents` and its rule chain reads, in order,
    ///   written rules (`Rule` as written, `Turned` with its sides exchanged),
    ///   each followed by its freshness conditions (`Fresh`, an atom's and a
    ///   variable's names), then derived rules (`Derived`, its peak's three
    ///   numerals), then ranks (`Rank`, an operation's name and a numeral),
    ///   then `End`. Each term is a `Var`, or an `App`, `Con` or `Tuple` over
    ///   its `Arg` chain; a symbol is interned by kind, name and argument
    ///   count, an `App` symbol taking the rank its name is given and every
    ///   other symbol a constructor's place. A rule's variables are numbered by
    ///   first occurrence on its left side, then on its right. A condition
    ///   holds of every instance, since no term names an atom, so the rules
    ///   read are the rules decided.
    /// - fails: [`TheoryRuleFault::Unreadable`] at the rule the chain stops
    ///   being readable at: a member out of that order, a condition before
    ///   every written rule, a term position holding no term, a field that is
    ///   no string where a name or numeral stands, a numeral not in its one
    ///   decimal spelling, or a second rank for one name.
    /// - panics: none.
    /// - intension: the chain walked in a loop and each term read from a
    ///   worklist, so no step recurses.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation with a written, a turned and a derived
    ///   rule and two ranks reads as its oriented rules, its peak and its
    ///   ranked operations; a rank before a rule, a derived rule before a
    ///   written one, a padded numeral and a second rank for one name are
    ///   unreadable at the rule they stand at.
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |rules| rules.peaks.len() <= rules.rules.len()))]
    #[inline]
    pub fn read(
        arena: &TermArena,
        presentation: ValueId,
    ) -> Result<Self, TheoryRuleRefusal>
    {
        Reader::new(arena).read(presentation)
    }

    /// Decide the rules: each well formed, each oriented by the path order
    /// over the stated ranks, each derived rule replaying its peak, and every
    /// critical pair joined.
    ///
    /// # Specification
    /// - requires: nothing — the rules may be arbitrary producer bytes.
    /// - ensures: `Ok(())` exactly when, in order: every rule is well formed
    ///   (both sides one term over known symbols, the left side headed by an
    ///   operation, instantiating nothing, and its variables numbered by first
    ///   occurrence, every right variable bound on the left); the path order
    ///   puts every left side above its right; each derived rule's peak names
    ///   two rules before it and an operation position of the outer one's left
    ///   side, other than the root of one rule overlapping itself, whose
    ///   critical pair's two normal forms under the rules before it are the
    ///   rule's two sides, up to renaming its variables; no rule instantiating
    ///   a variable overlaps or is overlapped by a rule; and every other
    ///   critical pair normalizes to one term under the rules that instantiate
    ///   nothing. Otherwise the first failing rule in that order and its fault;
    ///   a divergent or second-order overlap is named at its outer rule.
    /// - provides: the kernel's own decision that a presentation's rules are a
    ///   convergent rewriting system deciding the equations its written rules
    ///   generate, re-derived at every admission and replay.
    /// - fails: as `- ensures:`; [`TheoryRuleFault::Exhausted`] at the rule
    ///   being decided when `fuel` runs out.
    /// - panics: none.
    /// - measure: the rules, then the pairs, each step charged to `fuel`.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unit law converges and a second rule rewriting the
    ///   same call apart parts naming the pair; a group's inverse law diverges
    ///   alone and converges with the rules a completion derives, each
    ///   replaying its peak, while a derived rule naming the wrong peak, or
    ///   stating a side its peak does not reach, is refused at itself; a rule
    ///   the ranks do not decrease is unoriented and the same rule under a
    ///   higher rank for its head orients; each malformation is named; a `let`
    ///   instantiating its own argument converges, β is unoriented, and a
    ///   second-order rule overlapping another is refused at the overlap.
    /// - witness: `theory_rules::tests::a_unit_law_converges_and_a_second_unit_parts_from_it`
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    /// - witness: `theory_rules::tests::a_rule_the_ranks_do_not_decrease_is_unoriented`
    /// - witness: `theory_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| usize::from(refusal.rule) < self.rules.len()))]
    #[inline]
    pub fn decide(
        &self,
        fuel: &mut RewriteFuel,
    ) -> Result<(), TheoryRuleRefusal>
    {
        let refuse = |index: usize, fault| TheoryRuleRefusal {
            rule: RuleIndex::from(index),
            fault,
        };
        for (index, rule) in self.rules.iter().enumerate() {
            self.well_formed(rule)
                .map_err(|fault| refuse(index, fault))?;
        }
        let mut order = OrderBuffers::default();
        for (index, rule) in self.rules.iter().enumerate() {
            if self.path_greater(rule.left(), rule.right(), &mut order) == Verdict::Fails {
                return Err(refuse(index, TheoryRuleFault::Unoriented));
            }
        }
        let first = self.rules.len().saturating_sub(self.peaks.len());
        let mut work = PairBuffers::default();
        for (offset, &peak) in self.peaks.iter().enumerate() {
            let index = first.saturating_add(offset);
            let (Some(before), Some(rule)) = (self.rules.get(.. index), self.rules.get(index))
            else {
                return Err(refuse(index, TheoryRuleFault::NoPeak));
            };
            match self.joins(before, peak, rule, &mut work, fuel) {
                Ok(Verdict::Holds) => {},
                Ok(Verdict::Fails) => return Err(refuse(index, TheoryRuleFault::NoPeak)),
                Err(Exhausted) => return Err(refuse(index, TheoryRuleFault::Exhausted)),
            }
        }
        for (outer, rule) in self.rules.iter().enumerate() {
            for (position, &node) in rule.left().iter().enumerate() {
                if !matches!(node, TheoryNode::Symbol(_)) {
                    continue;
                }
                for inner in 0 .. self.rules.len() {
                    if position == 0 && inner == outer {
                        continue;
                    }
                    let peak = CriticalPeak {
                        outer: RuleIndex::from(outer),
                        position: SidePosition(position),
                        inner: RuleIndex::from(inner),
                    };
                    let second_order = rule.instantiates
                        || self
                            .rules
                            .get(inner)
                            .is_some_and(|other| other.instantiates);
                    if second_order {
                        match self.overlap(&self.rules, peak, &mut work, fuel) {
                            Ok(Verdict::Fails) => continue,
                            Ok(Verdict::Holds) => {
                                return Err(refuse(
                                    outer,
                                    TheoryRuleFault::Overlaps(RuleIndex::from(inner)),
                                ));
                            },
                            Err(Exhausted) => {
                                return Err(refuse(outer, TheoryRuleFault::Exhausted));
                            },
                        }
                    }
                    let joined = self
                        .pair(&self.rules, peak, &mut work, fuel)
                        .and_then(|pair| {
                            if pair == Verdict::Fails {
                                return Ok(Verdict::Holds);
                            }
                            self.normalize(
                                &self.rules,
                                &mut work.by_outer,
                                &mut work.bindings,
                                fuel,
                            )?;
                            self.normalize(
                                &self.rules,
                                &mut work.by_inner,
                                &mut work.bindings,
                                fuel,
                            )?;
                            Ok(Verdict::from(work.by_outer == work.by_inner))
                        });
                    match joined {
                        Ok(Verdict::Holds) => {},
                        Ok(Verdict::Fails) => {
                            return Err(refuse(
                                outer,
                                TheoryRuleFault::Diverges(RuleIndex::from(inner)),
                            ));
                        },
                        Err(Exhausted) => return Err(refuse(outer, TheoryRuleFault::Exhausted)),
                    }
                }
            }
        }
        Ok(())
    }

    /// The first critical pair of these rules whose two normal forms under
    /// them are `rule`'s two sides: the peak a completion that derived `rule`
    /// from these rules names for it.
    ///
    /// # Specification
    /// - requires: these rules are well formed.
    /// - ensures: [`Some`] with the first peak, in order of the outer rule, the
    ///   position and the inner rule, that [`Self::decide`] would replay for
    ///   `rule` appended after these rules; [`None`] when none does.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each rule a group's completion derives is found at a
    ///   peak of the rules before it, and the peaks found replay; a rule no
    ///   pair reaches has none.
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |peak| peak.is_none_or(|peak| usize::from(peak.outer) < self.rules.len() && usize::from(peak.inner) < self.rules.len())))]
    #[inline]
    pub fn peak_of(
        &self,
        rule: &TheoryRule,
        fuel: &mut RewriteFuel,
    ) -> Result<Option<CriticalPeak>, Exhausted>
    {
        let mut work = PairBuffers::default();
        for (outer, overlapped) in self.rules.iter().enumerate() {
            for (position, &node) in overlapped.left().iter().enumerate() {
                if !matches!(node, TheoryNode::Symbol(_)) {
                    continue;
                }
                for inner in 0 .. self.rules.len() {
                    if position == 0 && inner == outer {
                        continue;
                    }
                    let peak = CriticalPeak {
                        outer: RuleIndex::from(outer),
                        position: SidePosition(position),
                        inner: RuleIndex::from(inner),
                    };
                    if self.joins(&self.rules, peak, rule, &mut work, fuel)? == Verdict::Holds {
                        return Ok(Some(peak));
                    }
                }
            }
        }
        Ok(None)
    }

    /// The arity of `symbol`, none for a symbol outside the table.
    ///
    /// # Specification
    /// trivial.
    fn arity(
        &self,
        symbol: TheorySymbol,
    ) -> Option<FieldCount>
    {
        self.symbols.get(symbol.0).map(|&(_, arity)| arity)
    }

    /// The arity of `symbol` as a count, none outside the table counted as
    /// zero.
    ///
    /// # Specification
    /// trivial.
    fn width(
        &self,
        symbol: TheorySymbol,
    ) -> Position
    {
        Position(self.arity(symbol).map_or(0, usize::from))
    }

    /// Check `rule`'s shape.
    ///
    /// # Specification
    /// - ensures: `Ok(())` exactly when both sides are one term over known
    ///   symbols, the left side is headed by an operation and instantiates no
    ///   variable, its variables read in pre-order as first occurrences `0, 1,
    ///   2, …` with repeats of earlier ones, and every right-side variable and
    ///   instantiated variable is one of them.
    /// - panics: none.
    /// - executable: none — restating the shape is this walk over the sides.
    ///
    /// # Errors
    /// [`TheoryRuleFault::Malformed`] or [`TheoryRuleFault::Unbound`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`].
    /// - witness: `theory_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    fn well_formed(
        &self,
        rule: &TheoryRule,
    ) -> Result<(), TheoryRuleFault>
    {
        let headed = match rule.left().first() {
            Some(&TheoryNode::Symbol(symbol)) => matches!(
                self.symbols.get(symbol.0),
                Some(&(SymbolKind::Operation(_), _))
            ),
            Some(&(TheoryNode::Variable(_) | TheoryNode::Instance(..))) | None => false,
        };
        if !headed
            || rule
                .left()
                .iter()
                .any(|node| matches!(*node, TheoryNode::Instance(..)))
            || self.side_end(rule.left(), Position(0)) != Some(Position(rule.left().len()))
            || self.side_end(rule.right(), Position(0)) != Some(Position(rule.right().len()))
        {
            return Err(TheoryRuleFault::Malformed);
        }
        let mut bound = 0_usize;
        for &node in rule.left() {
            if let TheoryNode::Variable(variable) = node {
                let Ordinal(ordinal) = ordinal(variable);
                if ordinal == bound {
                    bound = bound.saturating_add(1);
                }
                else if ordinal > bound {
                    return Err(TheoryRuleFault::Malformed);
                }
            }
        }
        if rule.right().iter().any(|&node| {
            matches!(node, TheoryNode::Variable(variable) | TheoryNode::Instance(variable, _) if ordinal(variable).0 >= bound)
        }) {
            return Err(TheoryRuleFault::Unbound);
        }
        Ok(())
    }

    /// One past the end of the subterm of `side` starting at `start`, none
    /// when the side runs out first or names a symbol outside the table.
    ///
    /// # Specification
    /// trivial.
    fn side_end(
        &self,
        side: &[TheoryNode],
        start: Position,
    ) -> Option<Position>
    {
        let (mut at, mut owed) = (start.0, 1_usize);
        while let Some(next) = owed.checked_sub(1) {
            owed = match *side.get(at)? {
                TheoryNode::Symbol(symbol) => next.checked_add(usize::from(self.arity(symbol)?))?,
                TheoryNode::Instance(_, count) => next.checked_add(usize::from(count))?,
                TheoryNode::Variable(_) => next,
            };
            at = at.checked_add(1)?;
        }
        Some(Position(at))
    }

    /// Whether the higher-order recursive path order over the stated ranks
    /// puts `left` above `right`: the lexicographic path order, with every
    /// variable `right` instantiates read at a function type.
    ///
    /// # Specification
    /// - requires: both sides are well formed.
    /// - ensures: negative when `right` is a variable `right` instantiates
    ///   somewhere. Otherwise positive exactly when `left` is an application
    ///   some argument of which is equal to or above `right`; or `right` is an
    ///   application every argument of which `left` covers, and either `left`'s
    ///   symbol precedes `right`'s — an operation above an operation of a lower
    ///   rank, and above every constructor and results tuple — or the two are
    ///   one symbol and the first argument pair that differs, left to right, is
    ///   in the order; or `right` instantiates a variable that is an argument
    ///   of `left`, and `left` covers every argument of the instantiation.
    ///   `left` covers a term it is above, or one of its own arguments is equal
    ///   to or above. A variable is above nothing and no term above itself.
    /// - panics: none.
    /// - executable: none — the order is the table this fills; a predicate
    ///   restating it would be the function again.
    /// - intension: one table of every pair of positions of the two sides,
    ///   filled from the last positions up, so no comparison recurses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]: associativity, a unit law and an
    ///   inverse law orient, and a rule calling an operation of its head's rank
    ///   does not until the head ranks higher; a `let` instantiating its own
    ///   argument orients and β does not.
    /// - witness: `theory_rules::tests::a_rule_the_ranks_do_not_decrease_is_unoriented`
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    fn path_greater(
        &self,
        left: &[TheoryNode],
        right: &[TheoryNode],
        buffers: &mut OrderBuffers,
    ) -> Verdict
    {
        let columns = right.len();
        self.ends(left, &mut buffers.left_ends);
        self.ends(right, &mut buffers.right_ends);
        buffers.higher.clear();
        for &node in right {
            if let TheoryNode::Instance(variable, _) = node {
                let Ordinal(place) = ordinal(variable);
                if buffers.higher.len() <= place {
                    buffers.higher.resize(place.saturating_add(1), false);
                }
                if let Some(slot) = buffers.higher.get_mut(place) {
                    *slot = true;
                }
            }
        }
        let higher = &buffers.higher;
        let functional = |node: TheoryNode| matches!(node, TheoryNode::Variable(variable) if higher.get(ordinal(variable).0).copied().unwrap_or(false));
        buffers.table.clear();
        buffers
            .table
            .resize(left.len().saturating_mul(columns), Comparison::default());
        let precedes = |above: TheoryNode, below: TheoryNode| match (above, below) {
            (TheoryNode::Symbol(one), TheoryNode::Symbol(other)) => {
                match (self.symbols.get(one.0), self.symbols.get(other.0)) {
                    (
                        Some(&(SymbolKind::Operation(high), _)),
                        Some(&(SymbolKind::Operation(low), _)),
                    ) => high > low,
                    (Some(&(SymbolKind::Operation(_), _)), Some(&(SymbolKind::Constructor, _))) => {
                        true
                    },
                    _ => false,
                }
            },
            (TheoryNode::Symbol(_) | TheoryNode::Variable(_) | TheoryNode::Instance(..), _) => {
                false
            },
        };
        for row in (0 .. left.len()).rev() {
            for column in (0 .. columns).rev() {
                let (Some(&node), Some(&other)) = (left.get(row), right.get(column))
                else {
                    continue;
                };
                let rows = self.arguments(left, Position(row), &buffers.left_ends);
                let cols = self.arguments(right, Position(column), &buffers.right_ends);
                let at = |table: &[Comparison], row: Position, column: Position| {
                    row.0
                        .checked_mul(columns)
                        .and_then(|start| start.checked_add(column.0))
                        .and_then(|index| table.get(index).copied())
                        .unwrap_or_default()
                };
                let table = &buffers.table;
                let same = node == other;
                let equal = same
                    && rows
                        .clone()
                        .zip(cols.clone())
                        .all(|(one, two)| at(table, one, two).equal);
                // `node` covers a right argument it is above, or one of its
                // own arguments is equal to or above: the comparison a
                // variable read at a function type takes.
                let covers = |argument: Position| {
                    at(table, Position(row), argument).greater
                        || rows.clone().any(|own| {
                            let pair = at(table, own, argument);
                            pair.equal || pair.greater
                        })
                };
                let greater = matches!(node, TheoryNode::Symbol(_))
                    && !functional(other)
                    && (rows.clone().any(|argument| {
                        let pair = at(table, argument, Position(column));
                        pair.equal || pair.greater
                    }) || match other {
                        TheoryNode::Variable(_) => false,
                        TheoryNode::Instance(variable, _) => {
                            rows.clone()
                                .any(|own| left.get(own.0) == Some(&TheoryNode::Variable(variable)))
                                && cols.clone().all(covers)
                        },
                        TheoryNode::Symbol(_) => {
                            cols.clone().all(covers)
                                && if same {
                                    rows.clone()
                                        .zip(cols.clone())
                                        .map(|(one, two)| at(table, one, two))
                                        .find(|pair| !pair.equal)
                                        .is_some_and(|pair| pair.greater)
                                }
                                else {
                                    precedes(node, other)
                                }
                        },
                    });
                if let Some(cell) = row
                    .checked_mul(columns)
                    .and_then(|start| start.checked_add(column))
                    .and_then(|index| buffers.table.get_mut(index))
                {
                    *cell = Comparison { equal, greater };
                }
            }
        }
        Verdict::from(buffers.table.first().is_some_and(|pair| pair.greater))
    }

    /// The end of the subterm at every position of a well-formed `side`.
    ///
    /// # Specification
    /// trivial.
    fn ends(
        &self,
        side: &[TheoryNode],
        ends: &mut Vec<Position>,
    )
    {
        ends.clear();
        ends.resize(side.len(), Position(0));
        for (position, &node) in side.iter().enumerate().rev() {
            let mut end = position.saturating_add(1);
            let width = match node {
                TheoryNode::Symbol(symbol) => self.width(symbol).0,
                TheoryNode::Instance(_, count) => usize::from(count),
                TheoryNode::Variable(_) => 0,
            };
            for _ in 0 .. width {
                end = ends.get(end).map_or(end, |next| next.0);
            }
            if let Some(slot) = ends.get_mut(position) {
                *slot = Position(end);
            }
        }
    }

    /// The positions of the arguments of the node at `position` of `side`,
    /// left to right, by `ends`.
    ///
    /// # Specification
    /// trivial.
    fn arguments<'side>(
        &self,
        side: &'side [TheoryNode],
        position: Position,
        ends: &'side [Position],
    ) -> impl Iterator<Item = Position> + Clone + 'side
    {
        let arity = match side.get(position.0) {
            Some(&TheoryNode::Symbol(symbol)) => self.width(symbol).0,
            Some(&TheoryNode::Instance(_, count)) => usize::from(count),
            Some(&TheoryNode::Variable(_)) | None => 0,
        };
        let first = Position(position.0.saturating_add(1));
        core::iter::successors(Some(first), move |at| ends.get(at.0).copied()).take(arity)
    }

    /// Whether `peak`, over `before`, replays as `rule`: the two normal forms
    /// of its critical pair under `before` are `rule`'s sides, in either
    /// order, up to renaming the variables.
    ///
    /// # Specification
    /// - requires: `before` and `rule` are well formed.
    /// - ensures: positive exactly when the peak names two rules of `before`
    ///   and an operation position of the outer one's left side, other than the
    ///   root of one rule overlapping itself, their left sides unify there, and
    ///   the two reducts' normal forms under `before`, read with their
    ///   variables numbered by first occurrence across both, are `rule`'s left
    ///   and right sides so read, or its right and left.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — restating it needs the pair and the normal forms
    ///   this computes.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn joins(
        &self,
        before: &[TheoryRule],
        peak: CriticalPeak,
        rule: &TheoryRule,
        work: &mut PairBuffers,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        if usize::from(peak.outer) >= before.len()
            || usize::from(peak.inner) >= before.len()
            || (peak.position.0 == 0 && peak.outer == peak.inner)
            || self.pair(before, peak, work, fuel)? == Verdict::Fails
        {
            return Ok(Verdict::Fails);
        }
        self.normalize(before, &mut work.by_outer, &mut work.bindings, fuel)?;
        self.normalize(before, &mut work.by_inner, &mut work.bindings, fuel)?;
        canonical_flats(&work.by_outer, &work.by_inner, &mut work.canonical);
        canonical_sides(rule.left(), rule.right(), &mut work.stated);
        let split = rule.left().len();
        if (work.by_outer.len(), &work.canonical) == (split, &work.stated) {
            return Ok(Verdict::Holds);
        }
        canonical_flats(&work.by_inner, &work.by_outer, &mut work.canonical);
        Ok(Verdict::from(
            (work.by_inner.len(), &work.canonical) == (split, &work.stated),
        ))
    }

    /// Whether the overlap `peak` names over `rules` exists, the unifier left
    /// in `work`'s graph.
    ///
    /// # Specification
    /// - requires: the rules `peak` names are well formed.
    /// - ensures: positive exactly when the position holds an operation of the
    ///   outer rule's left side and the inner rule's left side unifies with the
    ///   subterm there, the two rules' variables kept apart and the unifier
    ///   passing the occurs check.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — the unifier this builds is the only witness of the
    ///   overlap.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]: the inverse law overlapping the
    ///   unit law and itself unify through a repeated variable, an overlap
    ///   whose unifier would be cyclic is none, and a `let` beside a rule that
    ///   rewrites under it overlaps it.
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    fn overlap(
        &self,
        rules: &[TheoryRule],
        peak: CriticalPeak,
        work: &mut PairBuffers,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        let (Some(outer), Some(inner)) = (
            rules.get(usize::from(peak.outer)),
            rules.get(usize::from(peak.inner)),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let position = Position(peak.position.0);
        if !matches!(outer.left().get(position.0), Some(&TheoryNode::Symbol(_))) {
            return Ok(Verdict::Fails);
        }
        work.graph.clear();
        work.outer_variables.clear();
        work.inner_variables.clear();
        let Some(root) = work.graph.load(
            self,
            outer.left(),
            &mut work.outer_variables,
            None,
            (&mut work.positions, &mut work.stack),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let Some(&at) = work.positions.get(position.0)
        else {
            return Ok(Verdict::Fails);
        };
        let Some(inner_root) = work.graph.load(
            self,
            inner.left(),
            &mut work.inner_variables,
            None,
            (&mut work.positions, &mut work.stack),
        )
        else {
            return Ok(Verdict::Fails);
        };
        if work.graph.unify(at, inner_root, &mut work.pairs, fuel)? == Verdict::Fails
            || work.graph.acyclic(root, &mut work.marks, &mut work.walk) == Verdict::Fails
        {
            return Ok(Verdict::Fails);
        }
        Ok(Verdict::Holds)
    }

    /// The critical pair `peak` names over `rules`, into `work`'s two terms.
    ///
    /// # Specification
    /// - requires: the rules `peak` names are well formed.
    /// - ensures: positive exactly when neither rule instantiates a variable
    ///   and [`Self::overlap`] is; `work.by_outer` then holds the outer rule's
    ///   right side under the unifier and `work.by_inner` its left side with
    ///   the inner rule's right side in place at the position, under the
    ///   unifier, each variable named by its node in the unifier.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — the unifier this builds is the only witness of the
    ///   overlap.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::overlap`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn pair(
        &self,
        rules: &[TheoryRule],
        peak: CriticalPeak,
        work: &mut PairBuffers,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        let (Some(outer), Some(inner)) = (
            rules.get(usize::from(peak.outer)),
            rules.get(usize::from(peak.inner)),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let position = Position(peak.position.0);
        let Some(end) = self.side_end(outer.left(), position)
        else {
            return Ok(Verdict::Fails);
        };
        if outer.instantiates
            || inner.instantiates
            || self.overlap(rules, peak, work, fuel)? == Verdict::Fails
        {
            return Ok(Verdict::Fails);
        }
        let (Some(by_outer), Some(replacement)) = (
            work.graph.load(
                self,
                outer.right(),
                &mut work.outer_variables,
                None,
                (&mut work.positions, &mut work.stack),
            ),
            work.graph.load(
                self,
                inner.right(),
                &mut work.inner_variables,
                None,
                (&mut work.positions, &mut work.stack),
            ),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let graft = Graft {
            span: Span {
                from: position,
                to: end,
            },
            node: replacement,
        };
        let Some(by_inner) = work.graph.load(
            self,
            outer.left(),
            &mut work.outer_variables,
            Some(graft),
            (&mut work.positions, &mut work.stack),
        )
        else {
            return Ok(Verdict::Fails);
        };
        work.graph
            .expand(by_outer, &mut work.by_outer, &mut work.stack, fuel)?;
        work.graph
            .expand(by_inner, &mut work.by_inner, &mut work.stack, fuel)?;
        Ok(Verdict::Holds)
    }

    /// Rewrite `term` to its normal form under the rules of `rules` that
    /// instantiate no variable.
    ///
    /// # Specification
    /// - requires: `rules` are well formed and oriented; `term` is one term.
    /// - ensures: `term` rewritten until no rule instantiating nothing matches
    ///   at any position: the redex rewritten next is the one starting last in
    ///   pre-order, and at one position the first such rule in order fires. A
    ///   left side's repeated variable matches only equal subterms. Each node
    ///   compared or copied costs one unit of `fuel`. A second-order rule fires
    ///   nowhere: its instantiation substitutes under a binder the first-order
    ///   term does not mark, and [`Self::decide`] has refused every overlap it
    ///   takes part in, so no critical pair needs it to join.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — a normal form is what this computes; checking one
    ///   is another pass of every rule at every position.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]: a group's critical pairs
    ///   normalize through its inverse law, which matches only a term whose two
    ///   arguments agree.
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn normalize(
        &self,
        rules: &[TheoryRule],
        term: &mut Vec<Flat>,
        bindings: &mut Vec<Option<Span>>,
        fuel: &mut RewriteFuel,
    ) -> Result<(), Exhausted>
    {
        let mut built: Vec<Flat> = Vec::new();
        let mut cursor = term.len();
        'rewrite: loop {
            while let Some(start) = cursor.checked_sub(1) {
                cursor = start;
                if !matches!(term.get(start), Some(&Flat::Symbol(..))) {
                    continue;
                }
                for rule in rules.iter().filter(|rule| !rule.instantiates) {
                    let Some(end) = matched(term, Position(start), rule.left(), bindings, fuel)?
                    else {
                        continue;
                    };
                    built.clear();
                    for &node in rule.right() {
                        fuel.charge()?;
                        match node {
                            TheoryNode::Symbol(symbol) => {
                                built.push(Flat::Symbol(symbol, self.width(symbol).0));
                            },
                            TheoryNode::Variable(variable) => {
                                if let Some(&Some(span)) = bindings.get(ordinal(variable).0) {
                                    for &copied in term.get(span.from.0 .. span.to.0).unwrap_or(&[])
                                    {
                                        fuel.charge()?;
                                        built.push(copied);
                                    }
                                }
                            },
                            // The filter above keeps every rule that
                            // instantiates a variable from firing.
                            TheoryNode::Instance(..) => {},
                        }
                    }
                    cursor = start.saturating_add(built.len());
                    let _replaced = term.splice(start .. end.0, built.iter().copied());
                    continue 'rewrite;
                }
            }
            return Ok(());
        }
    }
}

/// A variable's ordinal.
///
/// # Specification
/// trivial.
fn ordinal(variable: RuleVariable) -> Ordinal
{
    Ordinal(usize::try_from(u32::from(variable)).unwrap_or(usize::MAX))
}

/// A node's position in a side or a flattened term, or a child's place in
/// the unifier's child list or among a node's children.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Position(usize);

/// A node of the unifier's graph, by its place.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Node(usize);

/// A variable's ordinal, or its place among the variables first seen.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Ordinal(usize);

/// A number a peak or a rank spells.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Numeral(usize);

/// The positions a subterm spans: from its first to one past its last.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Span
{
    /// The first position.
    from: Position,
    /// One past the last.
    to: Position,
}

/// A subterm replaced by a node as a side loads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Graft
{
    /// The positions replaced.
    span: Span,
    /// The node standing in their place.
    node: Node,
}

/// Whether one of the decision's checks holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Verdict
{
    /// It holds.
    Holds,
    /// It does not.
    Fails,
}

impl From<bool> for Verdict
{
    /// The verdict `holds` states.
    ///
    /// # Specification
    /// trivial.
    fn from(holds: bool) -> Self
    {
        if holds { Self::Holds } else { Self::Fails }
    }
}

/// One node of a term the decision computes with: a symbol and its arity, or
/// a variable.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flat
{
    /// A symbol over its next `arity` subterms.
    Symbol(TheorySymbol, usize),
    /// A variable, by its node in the unifier's graph.
    Variable(Node),
}

/// One past the end of the subterm of `term` starting at `start`, none when
/// the term runs out first.
///
/// # Specification
/// trivial.
fn flat_end(
    term: &[Flat],
    start: Position,
) -> Option<Position>
{
    let (mut at, mut owed) = (start.0, 1_usize);
    while let Some(next) = owed.checked_sub(1) {
        owed = match *term.get(at)? {
            Flat::Symbol(_, arity) => next.checked_add(arity)?,
            Flat::Variable(_) => next,
        };
        at = at.checked_add(1)?;
    }
    Some(Position(at))
}

/// Where `left` matches `term` at `start`: the end of the matched subterm,
/// each variable's binding left in `bindings`.
///
/// # Specification
/// - requires: `left` is well formed and `term` is one term.
/// - ensures: [`Some`] exactly when every symbol of `left` stands at the
///   corresponding position of the subterm at `start` and a variable's every
///   occurrence binds equal subterms; `bindings` then holds each variable's
///   span of `term`, by ordinal.
/// - fails: [`Exhausted`] when `fuel` runs out first; one unit per node read or
///   compared.
/// - panics: none.
/// - executable: none — the bindings left behind are the match's only record.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryRules::decide`]: the inverse law matches a
///   product of an inverse and its own argument and no other.
/// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
fn matched(
    term: &[Flat],
    start: Position,
    left: &[TheoryNode],
    bindings: &mut Vec<Option<Span>>,
    fuel: &mut RewriteFuel,
) -> Result<Option<Position>, Exhausted>
{
    bindings.clear();
    let mut at = start.0;
    for &node in left {
        fuel.charge()?;
        match node {
            TheoryNode::Symbol(symbol) => match term.get(at) {
                Some(&Flat::Symbol(found, _)) if found == symbol => at = at.saturating_add(1),
                Some(&(Flat::Symbol(..) | Flat::Variable(_))) | None => return Ok(None),
            },
            // A pattern instantiating a variable matches nothing: a
            // well-formed left side instantiates none.
            TheoryNode::Instance(..) => return Ok(None),
            TheoryNode::Variable(variable) => {
                let Some(end) = flat_end(term, Position(at))
                else {
                    return Ok(None);
                };
                let Ordinal(ordinal) = ordinal(variable);
                if let Some(&Some(span)) = bindings.get(ordinal) {
                    let (Some(bound), Some(here)) =
                        (term.get(span.from.0 .. span.to.0), term.get(at .. end.0))
                    else {
                        return Ok(None);
                    };
                    if bound.len() != here.len() {
                        return Ok(None);
                    }
                    for (one, other) in bound.iter().zip(here) {
                        fuel.charge()?;
                        if one != other {
                            return Ok(None);
                        }
                    }
                }
                else {
                    if bindings.len() <= ordinal {
                        bindings.resize(ordinal.saturating_add(1), None);
                    }
                    if let Some(slot) = bindings.get_mut(ordinal) {
                        *slot = Some(Span {
                            from: Position(at),
                            to: end,
                        });
                    }
                }
                at = end.0;
            },
        }
    }
    Ok(Some(Position(at)))
}

/// One node of a term as two terms are compared up to their variables' names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Canonical
{
    /// A symbol.
    Symbol(TheorySymbol),
    /// A variable, by its first occurrence across both terms.
    Variable(Ordinal),
    /// An instantiation of a variable, by its first occurrence across both
    /// terms, over its argument count: no flat term holds one.
    Instance(Ordinal, FieldCount),
}

/// `first` then `second`, each variable renumbered by its first occurrence
/// across both, into `out`.
///
/// # Specification
/// trivial.
fn canonical_flats(
    first: &[Flat],
    second: &[Flat],
    out: &mut Vec<Canonical>,
)
{
    out.clear();
    let mut seen: Vec<Node> = Vec::new();
    for &node in first.iter().chain(second) {
        out.push(match node {
            Flat::Symbol(symbol, _) => Canonical::Symbol(symbol),
            Flat::Variable(variable) => Canonical::Variable(first_seen(&mut seen, variable)),
        });
    }
}

/// `left` then `right`, each variable renumbered by its first occurrence
/// across both, into `out`.
///
/// # Specification
/// trivial.
fn canonical_sides(
    left: &[TheoryNode],
    right: &[TheoryNode],
    out: &mut Vec<Canonical>,
)
{
    out.clear();
    let mut seen: Vec<Ordinal> = Vec::new();
    for &node in left.iter().chain(right) {
        out.push(match node {
            TheoryNode::Symbol(symbol) => Canonical::Symbol(symbol),
            TheoryNode::Variable(variable) => {
                Canonical::Variable(first_seen(&mut seen, ordinal(variable)))
            },
            TheoryNode::Instance(variable, count) => {
                Canonical::Instance(first_seen(&mut seen, ordinal(variable)), count)
            },
        });
    }
}

/// `key`'s place among the keys `seen` in order, appending it when new.
///
/// # Specification
/// trivial.
fn first_seen<K>(
    seen: &mut Vec<K>,
    key: K,
) -> Ordinal
where
    K: Copy + Eq,
{
    if let Some(place) = seen.iter().position(|&known| known == key) {
        return Ordinal(place);
    }
    seen.push(key);
    Ordinal(seen.len().saturating_sub(1))
}

/// One entry of the path order's table: whether two subterms are equal, and
/// whether the first is above the second.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default)]
struct Comparison
{
    /// The two subterms are one term.
    equal: bool,
    /// The first is above the second.
    greater: bool,
}

/// The buffers the path order fills, reused across rules.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct OrderBuffers
{
    /// Each left position's subterm end.
    left_ends: Vec<Position>,
    /// Each right position's subterm end.
    right_ends: Vec<Position>,
    /// The comparison of every pair of positions, by row.
    table: Vec<Comparison>,
    /// Whether the right side instantiates each variable, by ordinal.
    higher: Vec<bool>,
}

/// The buffers a critical pair is built and normalized in, reused across
/// pairs.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct PairBuffers
{
    /// The unifier's graph.
    graph: Graph,
    /// The outer rule's variables' nodes, by ordinal.
    outer_variables: Vec<Option<Node>>,
    /// The inner rule's variables' nodes, by ordinal.
    inner_variables: Vec<Option<Node>>,
    /// Each position of the side last loaded, by its node.
    positions: Vec<Node>,
    /// The loader's and the expander's stack.
    stack: Vec<Node>,
    /// The unifier's worklist.
    pairs: Vec<(Node, Node)>,
    /// The occurs check's marks.
    marks: Vec<Mark>,
    /// The occurs check's walk: each node open and its next child's place.
    walk: Vec<(Node, Position)>,
    /// The pair's side rewritten by the outer rule.
    by_outer: Vec<Flat>,
    /// The pair's side rewritten by the inner rule.
    by_inner: Vec<Flat>,
    /// A matched left side's bindings.
    bindings: Vec<Option<Span>>,
    /// The pair's normal forms, renumbered.
    canonical: Vec<Canonical>,
    /// A derived rule's sides, renumbered.
    stated: Vec<Canonical>,
}

/// One node of the unifier's graph.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum GraphNode
{
    /// A symbol over the `arity` children listed from `first`.
    Symbol
    {
        /// The symbol.
        symbol: TheorySymbol,
        /// Its first child's place in the child list.
        first: Position,
        /// Its child count.
        arity: usize,
    },
    /// A variable, bound to a node or free.
    Variable(Option<Node>),
}

/// A visit mark of the occurs check.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Mark
{
    /// Not reached.
    #[default]
    Unvisited,
    /// On the walk's current path.
    Open,
    /// Every node below it visited.
    Done,
}

/// Terms as a graph whose variables a unifier binds.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Graph
{
    /// The nodes.
    nodes: Vec<GraphNode>,
    /// Every symbol node's children, each run in argument order.
    children: Vec<Node>,
}

impl Graph
{
    /// Empty the graph.
    ///
    /// # Specification
    /// trivial.
    fn clear(&mut self)
    {
        self.nodes.clear();
        self.children.clear();
    }

    /// Load `side` into the graph, its variables shared through
    /// `variables`, with the subterm spanning `graft`'s positions replaced
    /// by its node; the root's node, and each position's in `positions`.
    ///
    /// # Specification
    /// - requires: `side` is well formed under `rules`' table.
    /// - ensures: [`Some`] with the root's node; a variable's node is the one
    ///   `variables` holds for its ordinal, made free and recorded when it
    ///   holds none. [`None`] when `side` is not one term or instantiates a
    ///   variable, which no node of the graph stands for.
    /// - panics: none.
    /// - executable: none — the nodes made are the graph's own state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn load(
        &mut self,
        rules: &TheoryRules,
        side: &[TheoryNode],
        variables: &mut Vec<Option<Node>>,
        graft: Option<Graft>,
        (positions, stack): (&mut Vec<Node>, &mut Vec<Node>),
    ) -> Option<Node>
    {
        stack.clear();
        positions.clear();
        positions.resize(side.len(), Node(usize::MAX));
        for (index, &node) in side.iter().enumerate().rev() {
            if let Some(Graft {
                span,
                node: grafted,
            }) = graft
                && index >= span.from.0
                && index < span.to.0
            {
                if index == span.from.0 {
                    stack.push(grafted);
                }
                continue;
            }
            let made = match node {
                TheoryNode::Variable(variable) => {
                    let Ordinal(ordinal) = ordinal(variable);
                    if variables.len() <= ordinal {
                        variables.resize(ordinal.saturating_add(1), None);
                    }
                    let slot = variables.get_mut(ordinal)?;
                    if let Some(made) = *slot {
                        made
                    }
                    else {
                        self.nodes.push(GraphNode::Variable(None));
                        let made = Node(self.nodes.len().saturating_sub(1));
                        *slot = Some(made);
                        made
                    }
                },
                TheoryNode::Symbol(symbol) => {
                    let arity = usize::from(rules.arity(symbol)?);
                    let first = Position(self.children.len());
                    for _ in 0 .. arity {
                        self.children.push(stack.pop()?);
                    }
                    self.nodes.push(GraphNode::Symbol {
                        symbol,
                        first,
                        arity,
                    });
                    Node(self.nodes.len().saturating_sub(1))
                },
                TheoryNode::Instance(..) => return None,
            };
            if let Some(slot) = positions.get_mut(index) {
                *slot = made;
            }
            stack.push(made);
        }
        let root = stack.pop()?;
        stack.is_empty().then_some(root)
    }

    /// The node `node` stands for: itself, or what its variable is bound to,
    /// followed through.
    ///
    /// # Specification
    /// trivial.
    fn resolve(
        &self,
        mut node: Node,
    ) -> Node
    {
        while let Some(&GraphNode::Variable(Some(bound))) = self.nodes.get(node.0) {
            node = bound;
        }
        node
    }

    /// The child at `offset` of the run starting at `first`.
    ///
    /// # Specification
    /// trivial.
    fn child(
        &self,
        first: Position,
        offset: Position,
    ) -> Option<Node>
    {
        self.children.get(first.0.checked_add(offset.0)?).copied()
    }

    /// Unify `one` with `other`, binding free variables.
    ///
    /// # Specification
    /// - ensures: positive exactly when no two symbols the walk meets in
    ///   corresponding places differ; each free variable met is then bound to
    ///   what stands opposite it. The occurs check is [`Self::acyclic`]'s.
    /// - fails: [`Exhausted`] when `fuel` runs out first; one unit per pair.
    /// - panics: none.
    /// - executable: none — the bindings made are the graph's own state.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn unify(
        &mut self,
        one: Node,
        other: Node,
        pairs: &mut Vec<(Node, Node)>,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        pairs.clear();
        pairs.push((one, other));
        while let Some((left, right)) = pairs.pop() {
            fuel.charge()?;
            let (left, right) = (self.resolve(left), self.resolve(right));
            if left == right {
                continue;
            }
            match (
                self.nodes.get(left.0).copied(),
                self.nodes.get(right.0).copied(),
            ) {
                (Some(GraphNode::Variable(_)), Some(_)) => {
                    if let Some(slot) = self.nodes.get_mut(left.0) {
                        *slot = GraphNode::Variable(Some(right));
                    }
                },
                (Some(GraphNode::Symbol { .. }), Some(GraphNode::Variable(_))) => {
                    if let Some(slot) = self.nodes.get_mut(right.0) {
                        *slot = GraphNode::Variable(Some(left));
                    }
                },
                (
                    Some(GraphNode::Symbol {
                        symbol,
                        first,
                        arity,
                    }),
                    Some(GraphNode::Symbol {
                        symbol: found,
                        first: other_first,
                        ..
                    }),
                ) => {
                    if symbol != found {
                        return Ok(Verdict::Fails);
                    }
                    for offset in 0 .. arity {
                        let (Some(child), Some(other_child)) = (
                            self.child(first, Position(offset)),
                            self.child(other_first, Position(offset)),
                        )
                        else {
                            return Ok(Verdict::Fails);
                        };
                        pairs.push((child, other_child));
                    }
                },
                (None, _) | (_, None) => return Ok(Verdict::Fails),
            }
        }
        Ok(Verdict::Holds)
    }

    /// Whether the term at `root`, its variables followed through their
    /// bindings, is finite: the occurs check.
    ///
    /// # Specification
    /// - ensures: positive exactly when no node reachable from `root` reaches
    ///   itself.
    /// - panics: none.
    /// - executable: none — restating it is this walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn acyclic(
        &self,
        root: Node,
        marks: &mut Vec<Mark>,
        walk: &mut Vec<(Node, Position)>,
    ) -> Verdict
    {
        marks.clear();
        marks.resize(self.nodes.len(), Mark::Unvisited);
        walk.clear();
        let start = self.resolve(root);
        if let Some(mark) = marks.get_mut(start.0) {
            *mark = Mark::Open;
        }
        walk.push((start, Position(0)));
        while let Some(&mut (node, ref mut next)) = walk.last_mut() {
            let child = match self.nodes.get(node.0) {
                Some(&GraphNode::Symbol { first, arity, .. }) if next.0 < arity => {
                    let child = self.child(first, *next);
                    *next = Position(next.0.saturating_add(1));
                    child
                },
                Some(&(GraphNode::Symbol { .. } | GraphNode::Variable(_))) | None => {
                    if let Some(mark) = marks.get_mut(node.0) {
                        *mark = Mark::Done;
                    }
                    let _done = walk.pop();
                    continue;
                },
            };
            let Some(child) = child.map(|child| self.resolve(child))
            else {
                continue;
            };
            match marks.get(child.0).copied() {
                Some(Mark::Open) => return Verdict::Fails,
                Some(Mark::Unvisited) => {
                    if let Some(mark) = marks.get_mut(child.0) {
                        *mark = Mark::Open;
                    }
                    walk.push((child, Position(0)));
                },
                Some(Mark::Done) | None => {},
            }
        }
        Verdict::Holds
    }

    /// The term at `root`, its variables followed through their bindings,
    /// flattened in pre-order into `out`.
    ///
    /// # Specification
    /// - requires: [`Self::acyclic`] holds at `root`.
    /// - ensures: one node per node reached; a free variable as its node.
    /// - fails: [`Exhausted`] when `fuel` runs out first; one unit per node.
    /// - panics: none.
    /// - executable: none — the flattening is this walk.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn expand(
        &self,
        root: Node,
        out: &mut Vec<Flat>,
        stack: &mut Vec<Node>,
        fuel: &mut RewriteFuel,
    ) -> Result<(), Exhausted>
    {
        out.clear();
        stack.clear();
        stack.push(root);
        while let Some(node) = stack.pop() {
            fuel.charge()?;
            let node = self.resolve(node);
            match self.nodes.get(node.0) {
                Some(&GraphNode::Symbol {
                    symbol,
                    first,
                    arity,
                }) => {
                    out.push(Flat::Symbol(symbol, arity));
                    for offset in (0 .. arity).rev() {
                        if let Some(child) = self.child(first, Position(offset)) {
                            stack.push(child);
                        }
                    }
                },
                Some(&GraphNode::Variable(_)) | None => out.push(Flat::Variable(node)),
            }
        }
        Ok(())
    }
}

/// What kind of node a symbol is interned from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Class
{
    /// An operation application.
    Operation,
    /// A constructor application.
    Constructor,
    /// A results tuple.
    Tuple,
    /// An atom's abstraction, its atom's name not part of its key, so two
    /// abstractions that differ only in the atom they name are one symbol.
    Abstraction,
}

/// What a term node over an argument chain applies.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Applied<'arena>
{
    /// A symbol, by its interning class and name.
    Symbol(Class, Option<&'arena StringLiteral>),
    /// An instantiation of a variable.
    Instance(RuleVariable),
}

/// Which members of the rule chain may come next.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Stage
{
    /// Written rules, or anything after them.
    Written,
    /// Derived rules, or ranks.
    Derived,
    /// Ranks alone.
    Ranks,
}

/// A symbol's interning key: its class, its name, and its argument count.
type SymbolKey<'arena> = (Class, Option<&'arena StringLiteral>, usize);

/// The buffers a rule's terms are read through, reused across rules.
///
/// # Specification
/// trivial.
#[derive(Default)]
struct ReadBuffers<'arena>
{
    /// The rule's variables, each by its place in first-occurrence order.
    variables: BTreeMap<&'arena StringLiteral, Ordinal>,
    /// The nodes still to read.
    stack: Vec<ValueId>,
    /// One node's arguments.
    arguments: Vec<ValueId>,
}

/// A reading of a presentation value's rule chain.
///
/// # Specification
/// trivial.
struct Reader<'arena>
{
    /// The arena the value lives in.
    arena: &'arena TermArena,
    /// Each interned symbol's key, in interning order.
    keys: Vec<SymbolKey<'arena>>,
    /// Each interned symbol, by its key.
    interned: BTreeMap<SymbolKey<'arena>, TheorySymbol>,
    /// The rules read so far.
    rules: Vec<TheoryRule>,
    /// The derived rules' peaks.
    peaks: Vec<CriticalPeak>,
    /// Each ranked operation's rank, by its name.
    ranks: BTreeMap<&'arena StringLiteral, OperationRank>,
}

impl<'arena> Reader<'arena>
{
    /// An empty reading over `arena`.
    ///
    /// # Specification
    /// trivial.
    fn new(arena: &'arena TermArena) -> Self
    {
        Self {
            arena,
            keys: Vec::new(),
            interned: BTreeMap::new(),
            rules: Vec::new(),
            peaks: Vec::new(),
            ranks: BTreeMap::new(),
        }
    }

    /// Read the rule chain of `presentation`, as [`TheoryRules::read`].
    ///
    /// # Specification
    /// - ensures: as [`TheoryRules::read`].
    /// - panics: none.
    /// - executable: none — [`TheoryRules::read`] carries the predicate.
    ///
    /// # Errors
    /// As [`TheoryRules::read`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`].
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    fn read(
        mut self,
        presentation: ValueId,
    ) -> Result<TheoryRules, TheoryRuleRefusal>
    {
        let tagged = |found: Option<(ConstructorTag, &'arena [ValueId])>| {
            found.map(|(tag, fields)| (usize::from(tag), fields))
        };
        let Some((tag::PRESENTS, &[_, _, rules])) = tagged(self.constructor(presentation))
        else {
            return Err(self.unreadable());
        };
        let mut at = rules;
        let mut stage = Stage::Written;
        let mut buffers = ReadBuffers::default();
        loop {
            let read = match tagged(self.constructor(at)) {
                Some((tag::END, &[])) => break,
                Some((tag::RULE, &[_, left, right, rest])) if stage == Stage::Written => {
                    self.rule(left, right, &mut buffers).map(|()| rest)
                },
                Some((tag::TURNED, &[_, left, right, rest])) if stage == Stage::Written => {
                    self.rule(right, left, &mut buffers).map(|()| rest)
                },
                Some((tag::FRESH, &[atom, term, rest]))
                    if stage == Stage::Written && !self.rules.is_empty() =>
                {
                    self.text(atom).and_then(|_| self.text(term)).map(|_| rest)
                },
                Some((tag::DERIVED, &[outer, position, inner, left, right, rest]))
                    if stage <= Stage::Derived =>
                {
                    stage = Stage::Derived;
                    let peak = match (
                        self.numeral(outer),
                        self.numeral(position),
                        self.numeral(inner),
                    ) {
                        (Some(outer), Some(position), Some(inner)) => Some(CriticalPeak {
                            outer: RuleIndex::from(outer.0),
                            position: SidePosition(position.0),
                            inner: RuleIndex::from(inner.0),
                        }),
                        _ => None,
                    };
                    peak.and_then(|peak| {
                        self.rule(left, right, &mut buffers)?;
                        self.peaks.push(peak);
                        Some(rest)
                    })
                },
                Some((tag::RANK, &[name, rank, rest])) => {
                    stage = Stage::Ranks;
                    let name = self.text(name);
                    let rank = self
                        .numeral(rank)
                        .and_then(|rank| u32::try_from(rank.0).ok());
                    match (name, rank) {
                        (Some(name), Some(rank)) => self
                            .ranks
                            .insert(name, OperationRank(rank))
                            .is_none()
                            .then_some(rest),
                        _ => None,
                    }
                },
                Some(_) | None => None,
            };
            at = read.ok_or_else(|| self.unreadable())?;
        }
        let symbols = self
            .keys
            .iter()
            .map(|&(class, name, arity)| {
                let kind = match (class, name) {
                    (Class::Operation, Some(name)) => {
                        SymbolKind::Operation(self.ranks.get(name).copied().unwrap_or_default())
                    },
                    (Class::Operation, None)
                    | (Class::Constructor | Class::Tuple | Class::Abstraction, _) => {
                        SymbolKind::Constructor
                    },
                };
                (kind, FieldCount::from(arity))
            })
            .collect();
        Ok(TheoryRules {
            symbols,
            rules: self.rules,
            peaks: self.peaks,
        })
    }

    /// The refusal at the rule the reading has reached.
    ///
    /// # Specification
    /// trivial.
    fn unreadable(&self) -> TheoryRuleRefusal
    {
        TheoryRuleRefusal {
            rule: RuleIndex::from(self.rules.len()),
            fault: TheoryRuleFault::Unreadable,
        }
    }

    /// The tag and fields of the constructor value `id`.
    ///
    /// # Specification
    /// trivial.
    fn constructor(
        &self,
        id: ValueId,
    ) -> Option<(ConstructorTag, &'arena [ValueId])>
    {
        let Value::Constructor {
            tag, ref fields, ..
        } = *self.arena.value(id)?
        else {
            return None;
        };
        Some((tag, fields.as_slice()))
    }

    /// The string value `id`.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &self,
        id: ValueId,
    ) -> Option<&'arena StringLiteral>
    {
        let Value::Literal(Literal::Text(ref text)) = *self.arena.value(id)?
        else {
            return None;
        };
        Some(text)
    }

    /// The number the string value `id` spells in decimal, none for any
    /// other spelling: empty, a non-digit, or a leading zero.
    ///
    /// # Specification
    /// trivial.
    fn numeral(
        &self,
        id: ValueId,
    ) -> Option<Numeral>
    {
        let digits: &str = self.text(id)?.as_ref();
        if digits.is_empty() || (digits.len() > 1 && digits.starts_with('0')) {
            return None;
        }
        digits
            .bytes()
            .try_fold(0_usize, |number, digit| {
                let value = digit.checked_sub(b'0').filter(|&value| value <= 9)?;
                number.checked_mul(10)?.checked_add(usize::from(value))
            })
            .map(Numeral)
    }

    /// Read the rule rewriting the term `left` to the term `right`.
    ///
    /// # Specification
    /// - ensures: [`Some`] with the rule appended, its variables numbered by
    ///   first occurrence on `left`, then on `right`; [`None`] when either term
    ///   is not one the code writes.
    /// - panics: none.
    /// - executable: none — [`TheoryRules::read`] carries the predicate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`].
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    fn rule(
        &mut self,
        left: ValueId,
        right: ValueId,
        buffers: &mut ReadBuffers<'arena>,
    ) -> Option<()>
    {
        buffers.variables.clear();
        let mut sides = (Vec::new(), Vec::new());
        self.term(left, buffers, &mut sides.0)?;
        self.term(right, buffers, &mut sides.1)?;
        self.rules
            .push(TheoryRule::new(sides.0.into(), sides.1.into()));
        Some(())
    }

    /// Read the term `root` in pre-order into `out`.
    ///
    /// # Specification
    /// - ensures: [`Some`] when every node reached is a `Var`, or an `App`,
    ///   `Con`, `Tuple`, `Inst` or `Abs` whose arguments are an `Arg` chain
    ///   ended by `End`; a variable, instantiated or not, takes its place among
    ///   `buffers.variables`, appended when new.
    /// - panics: none.
    /// - executable: none — [`TheoryRules::read`] carries the predicate.
    /// - intension: a worklist of the nodes still to read, so no step recurses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`].
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    fn term(
        &mut self,
        root: ValueId,
        buffers: &mut ReadBuffers<'arena>,
        out: &mut Vec<TheoryNode>,
    ) -> Option<()>
    {
        let tagged = |found: Option<(ConstructorTag, &'arena [ValueId])>| {
            found.map(|(tag, fields)| (usize::from(tag), fields))
        };
        buffers.stack.clear();
        buffers.stack.push(root);
        while let Some(node) = buffers.stack.pop() {
            let (applied, chain) = match tagged(self.constructor(node))? {
                (tag::VAR, &[name]) => {
                    let variable = variable(self.text(name)?, buffers)?;
                    out.push(TheoryNode::Variable(variable));
                    continue;
                },
                (tag::APP, &[name, chain]) => (
                    Applied::Symbol(Class::Operation, Some(self.text(name)?)),
                    chain,
                ),
                (tag::CON, &[name, chain]) => (
                    Applied::Symbol(Class::Constructor, Some(self.text(name)?)),
                    chain,
                ),
                (tag::TUPLE, &[chain]) => (Applied::Symbol(Class::Tuple, None), chain),
                (tag::ABS, &[name, chain]) => {
                    self.text(name)?;
                    (Applied::Symbol(Class::Abstraction, None), chain)
                },
                (tag::INST, &[name, chain]) => (
                    Applied::Instance(variable(self.text(name)?, buffers)?),
                    chain,
                ),
                _ => return None,
            };
            buffers.arguments.clear();
            let mut at = chain;
            loop {
                match tagged(self.constructor(at))? {
                    (tag::ARG, &[argument, rest]) => {
                        buffers.arguments.push(argument);
                        at = rest;
                    },
                    (tag::END, &[]) => break,
                    _ => return None,
                }
            }
            match applied {
                Applied::Symbol(class, name) => {
                    let key = (class, name, buffers.arguments.len());
                    let fresh = TheorySymbol(self.keys.len());
                    let symbol = *self.interned.entry(key).or_insert_with(|| {
                        self.keys.push(key);
                        fresh
                    });
                    out.push(TheoryNode::Symbol(symbol));
                },
                Applied::Instance(variable) => out.push(TheoryNode::Instance(
                    variable,
                    FieldCount::from(buffers.arguments.len()),
                )),
            }
            buffers.stack.extend(buffers.arguments.iter().rev());
        }
        Some(())
    }
}

/// The variable `name` names among `buffers.variables`, appended when new.
///
/// # Specification
/// trivial.
fn variable<'arena>(
    name: &'arena StringLiteral,
    buffers: &mut ReadBuffers<'arena>,
) -> Option<RuleVariable>
{
    let count = Ordinal(buffers.variables.len());
    let Ordinal(place) = *buffers.variables.entry(name).or_insert(count);
    u32::try_from(place).ok().map(RuleVariable::from)
}

#[cfg(test)]
mod tests;
