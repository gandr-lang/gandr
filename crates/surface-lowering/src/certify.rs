//! The rule certificate a `theory` block's core definition carries: what the
//! kernel needs to decide the block's rules by replay.
//!
//! The coincidence check oriented each written rule and completed the rules
//! with the ones their divergent pairs derived. [`rule_certificate`] states
//! that outcome in the terms the kernel reads: each written rule's direction,
//! each derived rule with the critical pair it joins, and each operation's
//! rank in the path order the check oriented by. A derived rule's peak is
//! found by the kernel's own reading of the rules
//! ([`gandr_kernel_term::TheoryRules::peak_of`]), so the peak the value names
//! is one the kernel replays.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::Above;
use gandr_kernel_term::BinderDistance;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::OperationRank;
use gandr_kernel_term::PRESENTATION_FUEL;
use gandr_kernel_term::PeakSearch;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleVariable;
use gandr_kernel_term::SymbolKind;
use gandr_kernel_term::TheoryNode;
use gandr_kernel_term::TheoryRule;
use gandr_kernel_term::TheoryRuleFault;
use gandr_kernel_term::TheoryRules;
use gandr_kernel_term::TheorySymbol;
use gandr_theory_levitation::DerivedFace;
use gandr_theory_levitation::DerivedPeak;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Freshness;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::Precedence;
use gandr_theory_levitation::RuleCertificate;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::RuleIndex;
use gandr_theory_levitation::RuleTurn;
use gandr_theory_levitation::SidePlace;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::naming_port;

use crate::coincide::Coincidence;
use crate::coincide::Joined;
use crate::desc_cells::DeclarationCells;
use crate::description::written::RuleDirection;

/// The certificate of the rules `cells` decided for `description`.
///
/// # Specification
/// - requires: `cells` is the coincidence check's outcome for `description`.
/// - ensures: one turn per oriented rule, [`RuleTurn::Turned`] exactly where
///   the order chose right to left; the rules completion derived in the
///   presented reading when it derived any there and the sequent reading's
///   otherwise, each with the first peak of the rules before it whose normal
///   forms are its sides, a written rule conditioned exactly as the kernel
///   reads it, stopping before the first rule no peak reaches; and each
///   operation the rules mention, of a positive rank in the precedence the
///   oriented rules and the ranking derived rules induce, in declaration order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a group's inverse law turns no rule, derives the rules
///   its completion derived each at a peak the kernel replays, and ranks its
///   operations so the kernel orients every rule; a block with no derived rule
///   carries its turns and ranks alone, and a block with no rule carries
///   nothing.
/// - witness: `certify::tests::a_groups_certificate_replays_in_the_kernel`
#[spec(ensures: |ref ret| ret.turns.len() == cells.directions.len())]
#[must_use]
pub fn rule_certificate<G>(
    description: &TheoryDesc<G>,
    cells: &DeclarationCells,
) -> RuleCertificate
where
    G: Clone,
{
    let turns: Vec<RuleTurn> = cells
        .directions
        .iter()
        .map(|&direction| match direction {
            RuleDirection::LeftToRight => RuleTurn::AsWritten,
            RuleDirection::RightToLeft => RuleTurn::Turned,
        })
        .collect();
    let derived: Vec<((FreeTerm, FreeTerm), Joined)> = match cells.coincidence {
        Coincidence::Joined(ref certificates) if !certificates.derived_terms.is_empty() => {
            certificates
                .derived_terms
                .iter()
                .map(|rule| (rule.rule.clone(), rule.joined))
                .collect()
        },
        Coincidence::Joined(ref certificates) => certificates
            .derived_commands
            .iter()
            .map(|rule| (rule.rule.clone(), rule.joined))
            .collect(),
        Coincidence::Unexamined | Coincidence::Orthogonal | Coincidence::Refused(_) => Vec::new(),
    };
    let mut oriented = description.clone();
    oriented.rules = cells.oriented.clone().into();
    let ranking: Vec<(FreeTerm, FreeTerm)> = derived
        .iter()
        .filter(|&&(_, joined)| joined == Joined::Ranking)
        .map(|&(ref rule, _)| rule.clone())
        .collect();
    let precedence = Precedence::with(&oriented, &ranking);
    let mut ranks: Vec<(Name, gandr_theory_levitation::Rank)> = precedence
        .ranks()
        .filter(|&(_, rank)| usize::from(rank) > 0)
        .map(|(name, rank)| (name.clone(), rank))
        .collect();
    let mut symbols = Symbols::new(&ranks);
    let nameable = Nameable::from(naming_port(description).is_some());
    let written: Vec<TheoryRule> = cells
        .oriented
        .iter()
        .map(|face| symbols.face(face, nameable))
        .collect();
    let derived_rules: Vec<TheoryRule> = derived
        .iter()
        .map(|&((ref left, ref right), _)| symbols.rule(left, right, &[], nameable))
        .collect();
    let mut kernel = TheoryRules::new(symbols.table(), written);
    let mentioned = symbols.operations();
    ranks.retain(|&(ref name, _)| mentioned.contains(name));
    let mut faces = Vec::with_capacity(derived.len());
    let mut search = PeakSearch::default();
    for (((left, right), _), rule) in derived.into_iter().zip(derived_rules) {
        let Ok(Some(peak)) = kernel.peak_of(
            &rule,
            &mut search,
            &mut RewriteFuel::from(PRESENTATION_FUEL),
        )
        else {
            break;
        };
        faces.push(DerivedFace {
            left,
            right,
            peak: DerivedPeak {
                outer: RuleIndex::from(usize::from(peak.outer)),
                position: SidePlace::from(usize::from(peak.position)),
                inner: RuleIndex::from(usize::from(peak.inner)),
            },
        });
        kernel.derive(rule, peak);
    }
    RuleCertificate {
        turns,
        derived: faces,
        ranks,
    }
}

/// The first critical pair of `description`'s rules and `derived`, one of
/// them instantiating a variable or conditioned, that the kernel's
/// second-order reading does not join: its two rules' places, the later
/// first, the written rules numbered before the derived ones.
///
/// # Specification
/// - requires: `description`'s rules are oriented.
/// - ensures: [`None`] exactly when [`TheoryRules::second_order`] accepts the
///   written rules, conditioned as [`rule_certificate`] conditions them,
///   followed by `derived`; else [`Some`] with the larger and the smaller of
///   the refused rule's place and its partner's, both the refused rule's when
///   the fault names no partner.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a relative monad's laws pass, and a `let` rule beside a
///   second rewriting its constant apart is named with that rule.
/// - witness: `coincide::tests::a_second_order_rule_overlapping_another_refuses_the_block`
#[spec(ensures: |ref ret| ret.is_none_or(|(later, earlier)| earlier <= later
    && usize::from(later) < description.rules.len().saturating_add(derived.len())))]
pub fn second_order_parts<G>(
    description: &TheoryDesc<G>,
    derived: &[&(FreeTerm, FreeTerm)],
) -> Option<(RuleIndex, RuleIndex)>
{
    let mut symbols = Symbols::new(&[]);
    let nameable = Nameable::from(naming_port(description).is_some());
    let mut rules: Vec<TheoryRule> = description
        .rules
        .iter()
        .map(|face| symbols.face(face, nameable))
        .collect();
    rules.extend(
        derived
            .iter()
            .map(|&&(ref left, ref right)| symbols.rule(left, right, &[], nameable)),
    );
    let refusal = TheoryRules::new(symbols.table(), rules)
        .second_order(&mut RewriteFuel::from(PRESENTATION_FUEL))
        .err()?;
    let outer = usize::from(refusal.rule);
    let inner = match refusal.fault {
        TheoryRuleFault::Diverges(inner) | TheoryRuleFault::Overlaps(inner) => usize::from(inner),
        TheoryRuleFault::Unreadable
        | TheoryRuleFault::Malformed
        | TheoryRuleFault::Unbound
        | TheoryRuleFault::Unoriented
        | TheoryRuleFault::NoPeak
        | TheoryRuleFault::Exhausted
        | TheoryRuleFault::UndecidedCondition => outer,
    };
    Some((
        RuleIndex::from(outer.max(inner)),
        RuleIndex::from(outer.min(inner)),
    ))
}

/// A symbol's interning key: its class, its name, and its argument count.
type SymbolKey<'term> = (Class, Option<&'term Name>, usize);

/// Whether a term of a block can name an atom or a variable one of its
/// binders binds, as [`naming_port`] finds a port taking one.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Nameable(bool);

/// The binder a name above a node is bound by.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binder
{
    /// An atom's abstraction, `bind a . t`.
    Abstraction,
    /// A binding field, its variable bound for the field's body.
    Field,
}

impl From<bool> for Nameable
{
    /// Nameable exactly when `nameable`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nameable: bool) -> Self
    {
        Self(nameable)
    }
}

/// The kernel's symbol table as the certificate's rules build it.
///
/// # Specification
/// trivial.
struct Symbols<'term>
{
    /// Each symbol's key, in interning order, as the kernel interns them.
    keys: Vec<SymbolKey<'term>>,
    /// Each interned symbol, by its key.
    interned: BTreeMap<SymbolKey<'term>, TheorySymbol>,
    /// Each ranked operation's rank, by its name.
    ranks: BTreeMap<&'term Name, gandr_theory_levitation::Rank>,
}

/// What a symbol is interned from.
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
    /// An atom's abstraction, keyed without its atom's name.
    Abstraction,
    /// An atom's occurrence, keyed by the number of binders between it and
    /// the one binding it.
    Occurrence(usize),
    /// A binding field, keyed without its variable's name.
    Field,
    /// A bound variable's occurrence, keyed by the number of binders between
    /// it and the one binding it.
    BoundVariable(usize),
}

impl<'term> Symbols<'term>
{
    /// An empty table whose operations take the ranks `ranks` gives them.
    ///
    /// # Specification
    /// trivial.
    fn new(ranks: &'term [(Name, gandr_theory_levitation::Rank)]) -> Self
    {
        Self {
            keys: Vec::new(),
            interned: BTreeMap::new(),
            ranks: ranks.iter().map(|&(ref name, rank)| (name, rank)).collect(),
        }
    }

    /// The name of every operation the rules read so far apply.
    ///
    /// # Specification
    /// trivial.
    fn operations(&self) -> BTreeSet<Name>
    {
        self.keys
            .iter()
            .filter_map(|&(class, name, _)| match class {
                Class::Operation => name.cloned(),
                Class::Constructor
                | Class::Tuple
                | Class::Abstraction
                | Class::Occurrence(_)
                | Class::Field
                | Class::BoundVariable(_) => None,
            })
            .collect()
    }

    /// The symbol table so far, each operation at its rank.
    ///
    /// # Specification
    /// trivial.
    fn table(&self) -> Vec<(SymbolKind, FieldCount)>
    {
        self.keys
            .iter()
            .map(|&(class, name, arity)| {
                let kind = match (class, name) {
                    (Class::Operation, Some(name)) => {
                        let rank = self.ranks.get(name).map_or(0, |&rank| usize::from(rank));
                        SymbolKind::Operation(OperationRank::from(
                            u32::try_from(rank).unwrap_or(u32::MAX),
                        ))
                    },
                    (Class::Operation, None) | (Class::Constructor | Class::Tuple, _) => {
                        SymbolKind::Constructor
                    },
                    (Class::Abstraction, _) => SymbolKind::Abstraction,
                    (Class::Occurrence(between), _) => {
                        SymbolKind::Occurrence(BinderDistance::from(between))
                    },
                    (Class::Field, _) => SymbolKind::Field,
                    (Class::BoundVariable(between), _) => {
                        SymbolKind::Bound(BinderDistance::from(between))
                    },
                };
                (kind, FieldCount::from(arity))
            })
            .collect()
    }

    /// The kernel's reading of the written rule `face`: as [`Self::rule`]
    /// reads its sides under the freshness conditions it states, and
    /// conditioned exactly where a term can name an atom and the face is.
    ///
    /// # Specification
    /// trivial.
    fn face(
        &mut self,
        face: &'term RuleFace,
        nameable: Nameable,
    ) -> TheoryRule
    {
        let rule = self.rule(&face.lhs, &face.rhs, &face.fresh, nameable);
        if nameable == Nameable(true) && bool::from(face.conditioned()) {
            rule.conditioned()
        }
        else {
            rule
        }
    }

    /// The kernel's reading of the rule `left` to `right`: its variables
    /// numbered by first occurrence on the left, then on the right; where a
    /// term can name an atom, each variable occurrence reading the atoms it
    /// may name under `fresh`, as [`TheoryRule::scoped`] reads them and the
    /// kernel reads them off the value.
    ///
    /// # Specification
    /// trivial.
    fn rule(
        &mut self,
        left: &'term FreeTerm,
        right: &'term FreeTerm,
        fresh: &'term [Freshness],
        nameable: Nameable,
    ) -> TheoryRule
    {
        let mut variables = BTreeMap::new();
        let mut held = Held::default();
        let left = self.side(left, &mut variables, &mut held);
        let right = self.side(right, &mut variables, &mut held);
        let rule = TheoryRule::new(left.into(), right.into());
        if nameable == Nameable(false) {
            return rule;
        }
        let fresh: Vec<(&Name, RuleVariable)> = fresh
            .iter()
            .filter_map(|condition| {
                variables
                    .get(&condition.term)
                    .map(|&variable| (&condition.atom, variable))
            })
            .collect();
        let mut start = 0;
        let above: Vec<&[Above<&Name>]> = held
            .ends
            .iter()
            .map(|&end| {
                let binders = held.binders.get(start .. end).unwrap_or_default();
                start = end;
                binders
            })
            .collect();
        rule.scoped(&above, &fresh)
    }

    /// `term` in pre-order, interning its symbols and numbering its
    /// variables among `variables`, an instantiated one as an instantiated
    /// variable is, and an occurrence by the number of binders between it and
    /// the innermost of its kind binding its name; the binders above each
    /// variable occurrence kept in `held`.
    ///
    /// # Specification
    /// trivial.
    fn side(
        &mut self,
        term: &'term FreeTerm,
        variables: &mut BTreeMap<&'term Name, RuleVariable>,
        held: &mut Held<'term>,
    ) -> Vec<TheoryNode>
    {
        let mut nodes = Vec::new();
        // Each node still to read, with the number of binders above it.
        let mut pending: Vec<(TermNode<'term>, usize)> = Vec::from([(term.to_node(), 0)]);
        let mut arguments: Vec<TermNode<'term>> = Vec::new();
        // The names the binders above the node read bind, each with its
        // binder.
        let mut atoms: Vec<(&'term Name, Binder)> = Vec::new();
        while let Some((node, depth)) = pending.pop() {
            arguments.clear();
            atoms.truncate(depth);
            let (class, name) = match node.view() {
                TermView::Var(name) => {
                    held.hold(&atoms);
                    nodes.push(TheoryNode::Variable(Self::variable(variables, name)));
                    continue;
                },
                TermView::Inst { name, args } => {
                    held.hold(&atoms);
                    arguments.extend(args);
                    nodes.push(TheoryNode::Instance(
                        Self::variable(variables, name),
                        FieldCount::from(arguments.len()),
                    ));
                    pending.extend(arguments.iter().rev().map(|&argument| (argument, depth)));
                    continue;
                },
                TermView::Op { name, args } => {
                    arguments.extend(args);
                    (Class::Operation, Some(name))
                },
                TermView::Ctor { name, args } => {
                    arguments.extend(args);
                    (Class::Constructor, Some(name))
                },
                TermView::Results { args } => {
                    arguments.extend(args);
                    (Class::Tuple, None)
                },
                TermView::Abs { atom, args } => {
                    arguments.extend(args);
                    atoms.push((atom, Binder::Abstraction));
                    (Class::Abstraction, None)
                },
                TermView::Lam { var, args } => {
                    arguments.extend(args);
                    atoms.push((var, Binder::Field));
                    (Class::Field, None)
                },
                TermView::Atom(name) | TermView::Bound(name) => {
                    let binder = if matches!(node.view(), TermView::Bound(_)) {
                        Binder::Field
                    }
                    else {
                        Binder::Abstraction
                    };
                    let between = atoms
                        .iter()
                        .rev()
                        .position(|&above| above == (name, binder))
                        .unwrap_or(atoms.len());
                    match binder {
                        Binder::Field => (Class::BoundVariable(between), None),
                        Binder::Abstraction => (Class::Occurrence(between), None),
                    }
                },
            };
            let key = (class, name, arguments.len());
            let fresh = TheorySymbol::from(self.keys.len());
            let symbol = *self.interned.entry(key).or_insert_with(|| {
                self.keys.push(key);
                fresh
            });
            nodes.push(TheoryNode::Symbol(symbol));
            let below = if matches!(class, Class::Abstraction | Class::Field) {
                depth.saturating_add(1)
            }
            else {
                depth
            };
            pending.extend(arguments.iter().rev().map(|&argument| (argument, below)));
        }
        nodes
    }

    /// The kernel's number for the variable `name`: its first occurrence's
    /// place among `variables`, appended when new.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        variables: &mut BTreeMap<&'term Name, RuleVariable>,
        name: &'term Name,
    ) -> RuleVariable
    {
        let fresh = RuleVariable::from(u32::try_from(variables.len()).unwrap_or(u32::MAX));
        *variables.entry(name).or_insert(fresh)
    }
}

/// The binders above each variable occurrence of a rule, outermost first,
/// end to end, as [`Symbols::side`] reads its sides.
///
/// # Specification
/// trivial.
#[derive(Default)]
struct Held<'term>
{
    /// Every occurrence's binders, end to end.
    binders: Vec<Above<&'term Name>>,
    /// One past each occurrence's last binder.
    ends: Vec<usize>,
}

impl<'term> Held<'term>
{
    /// Keep `atoms`, the binders above the next occurrence, outermost first,
    /// each with the name it binds.
    ///
    /// # Specification
    /// trivial.
    fn hold(
        &mut self,
        atoms: &[(&'term Name, Binder)],
    )
    {
        self.binders
            .extend(atoms.iter().map(|&(name, binder)| match binder {
                Binder::Field => Above::Field,
                Binder::Abstraction => Above::Atom(name),
            }));
        self.ends.push(self.binders.len());
    }
}

#[cfg(test)]
mod tests;
