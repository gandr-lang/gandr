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
//! is one the kernel replays. Over an indexed sort completion ran over terms
//! carrying their indices, which is the reading the kernel decides by: the
//! peaks are found among the written rules read with their indices, and each
//! derived rule is stated without them, as the kernel re-derives them.

use alloc::borrow::Cow;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::Above;
use gandr_kernel_term::BinderDistance;
use gandr_kernel_term::Exhausted;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::NormalNode;
use gandr_kernel_term::OperationRank;
use gandr_kernel_term::PRESENTATION_FUEL;
use gandr_kernel_term::PeakSearch;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RowExtent;
use gandr_kernel_term::RowLabel;
use gandr_kernel_term::RuleRow;
use gandr_kernel_term::RuleVariable;
use gandr_kernel_term::SymbolKind;
use gandr_kernel_term::TheoryNode;
use gandr_kernel_term::TheoryRule;
use gandr_kernel_term::TheoryRuleFault;
use gandr_kernel_term::TheoryRules;
use gandr_kernel_term::TheorySymbol;
use gandr_theory_levitation::AbstractionDepth;
use gandr_theory_levitation::DerivedFace;
use gandr_theory_levitation::DerivedPeak;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Freshness;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::Precedence;
use gandr_theory_levitation::RowTail;
use gandr_theory_levitation::RuleCertificate;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::RuleIndex;
use gandr_theory_levitation::RuleTurn;
use gandr_theory_levitation::SidePlace;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::naming_port;
use quenchant_shape::shape::Maybe;

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
///   Where the presented reading carries indices, the peaks are those of the
///   written rules read with them
///   ([`Indexing::face`](gandr_theory_computads::Indexing::face)) and each
///   derived rule is stated stripped of them
///   ([`Indexing::strip`](gandr_theory_computads::Indexing::strip)).
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
    let derived: Vec<((FreeTerm, FreeTerm), Joined)> = derived(cells)
        .into_iter()
        .map(|(rule, joined)| (rule.clone(), joined))
        .collect();
    // The indices the derived rules carry: those of the presented reading,
    // when completion derived its rules there.
    let indexing = match (&cells.coincidence, &cells.presented) {
        (&Coincidence::Joined(ref certificates), &Maybe::Present(ref presented))
            if !certificates.derived_terms.is_empty() =>
        {
            match presented.indexing {
                Maybe::Present(ref indexing) => Some(indexing),
                Maybe::Absent(_) => None,
            }
        },
        (
            &(Coincidence::Unexamined
            | Coincidence::Orthogonal
            | Coincidence::Refused(_)
            | Coincidence::Joined(_)),
            &(Maybe::Present(_) | Maybe::Absent(_)),
        ) => None,
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
    let read: Vec<Cow<'_, RuleFace>> = cells
        .oriented
        .iter()
        .map(|face| match indexing.map(|indexing| indexing.face(face)) {
            Some(Ok(indexed)) => Cow::Owned(indexed),
            Some(Err(_)) | None => Cow::Borrowed(face),
        })
        .collect();
    let mut symbols = Symbols::new(&ranks);
    let nameable = Nameable::from(naming_port(description).is_some());
    let written: Vec<TheoryRule> = read
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
            left: indexing.map_or_else(|| left.clone(), |indexing| indexing.strip(&left)),
            right: indexing.map_or_else(|| right.clone(), |indexing| indexing.strip(&right)),
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

/// The normal form `call` reaches in the kernel's second-order reading.
///
/// The rules are those `cells` oriented and derived for `description`, the
/// reading [`TheoryRules::second_order_normal_form`], and the normal form is
/// written back as a free term.
///
/// # Specification
/// - requires: `cells` is the coincidence check's outcome for `description`;
///   `call` writes no variable.
/// - ensures: [`Some`] with the normal form, the written rules read as
///   [`rule_certificate`] reads them followed by the derived ones and the call
///   read as a rule side is, each abstraction and binding field written back
///   naming the canonical atom of its depth and each occurrence its binder's;
///   [`None`] where the kernel reads the call as no closed term or a rule's
///   instance as ill formed.
/// - fails: [`Exhausted`] when `fuel` runs out first.
/// - panics: none.
/// - executable: none — the normal form is what the kernel's reading computes;
///   checking one is another normalization of the call.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — β at a binding field and a rule instantiating its
///   continuation below an operation reach the normal forms substitution gives,
///   a binder the normal form keeps reading back at its depth.
/// - witness: `coincide::tests::an_instantiating_rule_fires_at_an_inspected_call_2966`
pub fn second_order_normal_form<G>(
    description: &TheoryDesc<G>,
    cells: &DeclarationCells,
    call: &FreeTerm,
    fuel: &mut RewriteFuel,
) -> Result<Option<FreeTerm>, Exhausted>
{
    let mut symbols = Symbols::new(&[]);
    let nameable = Nameable::from(naming_port(description).is_some());
    let mut rules: Vec<TheoryRule> = cells
        .oriented
        .iter()
        .map(|face| symbols.face(face, nameable))
        .collect();
    rules.extend(
        derived(cells)
            .into_iter()
            .map(|(&(ref left, ref right), _)| symbols.rule(left, right, &[], nameable)),
    );
    let term = symbols.side(call, &mut BTreeMap::new(), &mut Held::default());
    let Some(normal) =
        TheoryRules::new(symbols.table(), rules).second_order_normal_form(&term, fuel)?
    else {
        return Ok(None);
    };
    Ok(symbols.written(&normal))
}

/// The rules completion derived for `cells`, each with how its pair joined:
/// the presented reading's when it derived any there, else the sequent
/// reading's.
///
/// # Specification
/// trivial.
fn derived(cells: &DeclarationCells) -> Vec<(&(FreeTerm, FreeTerm), Joined)>
{
    match cells.coincidence {
        Coincidence::Joined(ref certificates) if !certificates.derived_terms.is_empty() => {
            certificates
                .derived_terms
                .iter()
                .map(|rule| (&rule.rule, rule.joined))
                .collect()
        },
        Coincidence::Joined(ref certificates) => certificates
            .derived_commands
            .iter()
            .map(|rule| (&rule.rule, rule.joined))
            .collect(),
        Coincidence::Unexamined | Coincidence::Orthogonal | Coincidence::Refused(_) => Vec::new(),
    }
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
    /// Each theory a row names, by its label: its place in first-naming
    /// order, as the kernel labels them.
    labels: BTreeMap<&'term Name, RowLabel>,
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
            labels: BTreeMap::new(),
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
    /// reads its sides under the freshness conditions it states, conditioned
    /// exactly where a term can name an atom and the face is, and firing in
    /// the rows its row describes, each theory labelled as the kernel labels
    /// it off the value.
    ///
    /// # Specification
    /// trivial.
    fn face(
        &mut self,
        face: &'term RuleFace,
        nameable: Nameable,
    ) -> TheoryRule
    {
        let mut rule = self.rule(&face.lhs, &face.rhs, &face.fresh, nameable);
        if nameable == Nameable(true) && bool::from(face.conditioned()) {
            rule = rule.conditioned();
        }
        if let Maybe::Present(ref under) = face.under {
            let labels = &mut self.labels;
            let row: Vec<RowLabel> = under
                .theories
                .iter()
                .map(|theory| {
                    let next = RowLabel::from(u32::try_from(labels.len()).unwrap_or(u32::MAX));
                    *labels.entry(theory).or_insert(next)
                })
                .collect();
            let extent = match under.tail {
                RowTail::Closed => RowExtent::Exactly,
                RowTail::Open => RowExtent::AtLeast,
            };
            rule = rule.under(RuleRow::new(row, extent));
        }
        rule
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

    /// The free term the kernel's `nodes` write: each symbol by the key it
    /// was interned under, each abstraction and binding field naming the
    /// canonical atom of its depth, and each occurrence the name its binder
    /// names; [`None`] where a node names no symbol the table interned or an
    /// occurrence's, an occurrence counts past every binder above it, or the
    /// nodes are no one whole term.
    ///
    /// # Specification
    /// trivial.
    fn written(
        &self,
        nodes: &[NormalNode],
    ) -> Option<FreeTerm>
    {
        let key = |node: NormalNode| match node {
            NormalNode::Symbol(symbol) => self.keys.get(usize::from(symbol)).copied(),
            NormalNode::Atom(_) | NormalNode::Bound(_) => None,
        };
        // Each node's depth: the binders above it.
        let mut depths = Vec::with_capacity(nodes.len());
        // Each open node's arguments still to come, and whether it binds over
        // them.
        let mut open: Vec<(usize, bool)> = Vec::new();
        for &node in nodes {
            while let Some(&(0, _)) = open.last() {
                open.truncate(open.len().saturating_sub(1));
            }
            depths.push(open.iter().filter(|&&(_, binds)| binds).count());
            if let Some(&mut (ref mut left, _)) = open.last_mut() {
                *left = left.saturating_sub(1);
            }
            if let Some((class, _, arity)) = key(node)
                && arity > 0
            {
                open.push((arity, matches!(class, Class::Abstraction | Class::Field)));
            }
        }
        let mut built: Vec<FreeTerm> = Vec::with_capacity(nodes.len());
        for (&node, &depth) in nodes.iter().zip(&depths).rev() {
            let binder = |level: usize| FreeTerm::canonical_atom(AbstractionDepth::from(level));
            let occurrence = |distance: BinderDistance| {
                depth
                    .checked_sub(usize::from(distance))?
                    .checked_sub(1)
                    .map(binder)
            };
            let term = match node {
                NormalNode::Atom(distance) => FreeTerm::atom(occurrence(distance)?),
                NormalNode::Bound(distance) => FreeTerm::bound(occurrence(distance)?),
                NormalNode::Symbol(_) => {
                    let (class, name, arity) = key(node)?;
                    let split = built.len().checked_sub(arity)?;
                    let mut arguments: Vec<FreeTerm> = built.drain(split ..).rev().collect();
                    match class {
                        Class::Operation => FreeTerm::op(name?.clone(), arguments),
                        Class::Constructor => FreeTerm::ctor(name?.clone(), arguments),
                        Class::Tuple => FreeTerm::results(arguments),
                        Class::Abstraction => FreeTerm::abs(binder(depth), arguments.pop()?),
                        Class::Field => FreeTerm::lam(binder(depth), arguments.pop()?),
                        Class::Occurrence(_) | Class::BoundVariable(_) => return None,
                    }
                },
            };
            built.push(term);
        }
        let whole = built.pop()?;
        built.is_empty().then_some(whole)
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
