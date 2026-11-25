//! The probe of the mixed pairs: each ruled definition of an admitted source
//! whose rules match a constructor of a presented type with rules, read in
//! three ways.
//!
//! The rules of the presented type are the lower stratum, and the rules of
//! the operation are the higher one. A mixed pair is a rule of the operation
//! and a rule of the presented type whose left side unifies with a pattern
//! of the operation's left side below its root.
//!
//! 1. The decision of the kernel, [`OperationRules::converge`], over the
//!    declarations below the definition. It forms each mixed pair, the
//!    symmetry of the presented type included, and joins its two reducts by
//!    the rules as written.
//! 2. The replay of the source by the kernel, [`Environment::replay`]. It
//!    holds the obligation that a case over a presented type respects the
//!    rules of the type, `KernelError::RuleNotRespected`, beside the decision
//!    of item 1.
//! 3. The test of the normalization of stratified rewriting. At each mixed
//!    pair, with its most general unifier, both sides of the operation's rule
//!    go to their normal forms by the lower stratum, modulo each symmetry of
//!    it. The pair is in the stratum when one rule of the operation matches
//!    the normal left side modulo the symmetries, and its right side goes to
//!    the normal right side. The test holds when each mixed pair is in the
//!    stratum: the normalization then does not change the stratum.
//!
//! The contexts of a rule are the unifiers of its mixed pairs. For terms,
//! the most general unifiers are one finite set, and each other context is
//! an instance of one of them. So the test needs no bound on the size of a
//! context.
//!
//! # References
//!
//! - `vault:01a213f1-00b3-765d-b3f9-135dd191549f` — background: the two
//!   questions on a symmetry, and the units that each answer starts.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::OperationNode;
use gandr_kernel_term::OperationRuleFault;
use gandr_kernel_term::OperationRules;
use gandr_kernel_term::Overlapped;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleScope;
use gandr_kernel_term::SourceRank;
use gandr_kernel_term::TermArena;

use super::APART;
use super::Node;
use super::System;
use super::Term;
use super::at;
use super::matched;
use super::named;
use super::positions;
use super::read;
use super::rebuilt;
use super::resolved;
use super::substituted;
use super::tree;
use super::unifiers;

/// The fuel of the decision of item 1: the fuel of an admission.
const FUEL: u64 = 1 << 22;

/// A symbol of the terms of one probe.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Symbol
{
    /// The constructor `tag` of the data declaration at `family`.
    Constructor(ConstantIndex, ConstructorTag),
    /// The definition at its position.
    Operation(ConstantIndex),
    /// A results tuple of this count.
    Results(FieldCount),
}

/// The symbols of one probe, each with its place and its arity.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Symbols
{
    /// The place of each symbol.
    places: BTreeMap<Symbol, usize>,
    /// The arity of each symbol, by its place.
    arities: Vec<usize>,
}

impl Symbols
{
    /// The place of `symbol` over `arity` arguments, given at its first use.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &mut self,
        symbol: Symbol,
        arity: usize,
    ) -> usize
    {
        let next = self.arities.len();
        let place = *self.places.entry(symbol).or_insert(next);
        if place == next {
            self.arities.push(arity);
        }
        place
    }

    /// The side `nodes` of a rule of the operation, as nodes of the oracle;
    /// none when a constructor names no declaration of `scope`.
    ///
    /// # Specification
    /// trivial.
    fn operation_side(
        &mut self,
        nodes: &[OperationNode],
        scope: &Below<'_>,
    ) -> Option<Vec<Node>>
    {
        nodes
            .iter()
            .map(|&node| match node {
                OperationNode::Operation { constant, arity } => Some(Node::Symbol(self.place(
                    Symbol::Operation(constant),
                    usize::from(arity),
                ))),
                OperationNode::Constructor { family, tag } => {
                    let fields = scope.fields(family, tag)?;
                    Some(Node::Symbol(self.place(
                        Symbol::Constructor(family, tag),
                        usize::from(fields),
                    )))
                },
                OperationNode::Results(count) => Some(Node::Symbol(
                    self.place(Symbol::Results(count), usize::from(count)),
                )),
                OperationNode::Variable(variable) => Some(Node::Variable(u32::from(variable))),
            })
            .collect()
    }
}

/// The declarations below a ruled definition, as its rules read them in a
/// replay from the first declaration: each one ranked at its position.
///
/// # Specification
/// trivial.
struct Below<'declarations>(&'declarations [MarkedDeclaration]);

impl RuleScope for Below<'_>
{
    /// The field count of a constructor of a declaration below.
    ///
    /// # Specification
    /// trivial.
    fn fields(
        &self,
        family: ConstantIndex,
        tag: ConstructorTag,
    ) -> Option<FieldCount>
    {
        match *self.0.get(usize::from(family))?.declaration().content() {
            DeclarationContent::Data {
                ref constructors, ..
            } => constructors
                .get(usize::from(tag))
                .map(|fields| FieldCount::from(fields.len())),
            DeclarationContent::Codata { .. }
            | DeclarationContent::Def { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::LiteralIdentity { .. }
            | DeclarationContent::AbstractType { .. } => None,
        }
    }

    /// The presentation of a data declaration below.
    ///
    /// # Specification
    /// trivial.
    fn presentation(
        &self,
        family: ConstantIndex,
    ) -> Option<&Presentation>
    {
        let declaration = self.0.get(usize::from(family))?.declaration();
        matches!(*declaration.content(), DeclarationContent::Data { .. })
            .then(|| declaration.presentation())
    }

    /// The rules of a ruled definition below.
    ///
    /// # Specification
    /// trivial.
    fn rules(
        &self,
        constant: ConstantIndex,
    ) -> Option<&OperationRules>
    {
        let rules = self.0.get(usize::from(constant))?.declaration().operation_rules();
        (!rules.rules().is_empty()).then_some(rules)
    }

    /// The rank of a declaration below: its position.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        &self,
        constant: ConstantIndex,
    ) -> Option<SourceRank>
    {
        (usize::from(constant) < self.0.len()).then(|| SourceRank::from(constant))
    }
}

/// The verdicts of the probe on one ruled definition.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Probe
{
    /// The name of the definition.
    name: String,
    /// The count of its mixed pairs.
    mixed: usize,
    /// The verdict of item 1.
    converge: &'static str,
    /// The verdict of item 2.
    replay: String,
    /// The verdict of item 3.
    normalization: &'static str,
}

/// The families of the constructors that `rules` match below the root of a
/// left side, whose presentation holds a rule.
///
/// # Specification
/// trivial.
fn matched_families(
    rules: &OperationRules,
    scope: &Below<'_>,
) -> BTreeSet<ConstantIndex>
{
    rules
        .rules()
        .iter()
        .flat_map(|rule| rule.left().iter().skip(1))
        .filter_map(|&node| match node {
            OperationNode::Constructor { family, .. } => Some(family),
            OperationNode::Operation { .. }
            | OperationNode::Results(_)
            | OperationNode::Variable(_) => None,
        })
        .filter(|&family| {
            scope
                .presentation(family)
                .is_some_and(|presentation| !presentation.rules().is_empty())
        })
        .collect()
}

/// The lower stratum: the rules of each presentation of `families`, each
/// symmetry read as the commutativity of its constructor; beside it the
/// symmetries as rules, which item 1 reads as written.
///
/// # Specification
/// trivial.
fn lower(
    families: &BTreeSet<ConstantIndex>,
    scope: &Below<'_>,
    symbols: &mut Symbols,
) -> Option<(System, Vec<(Term, Term)>)>
{
    let mut stratum = System {
        name: String::new(),
        symmetric: BTreeSet::new(),
        rules: Vec::new(),
        unread: 0,
    };
    let mut written = Vec::new();
    for &family in families {
        let presentation = scope.presentation(family)?;
        let mut sides = Vec::new();
        for rule in presentation.rules() {
            let mut side = |nodes: &[RuleNode]| -> Option<Vec<Node>> {
                nodes
                    .iter()
                    .map(|&node| match node {
                        RuleNode::Constructor(tag) => {
                            let fields = scope.fields(family, tag)?;
                            Some(Node::Symbol(symbols.place(
                                Symbol::Constructor(family, tag),
                                usize::from(fields),
                            )))
                        },
                        RuleNode::Variable(variable) => Some(Node::Variable(u32::from(variable))),
                    })
                    .collect()
            };
            let left = side(rule.left())?;
            let right = side(rule.right())?;
            sides.push((left, right));
        }
        let arities = &symbols.arities;
        let (system, fault) = read(String::new(), &sides, |symbol| arities.get(symbol).copied(), 0);
        if fault.is_some() {
            return None;
        }
        for &(ref left, ref right) in &sides {
            let arity = |symbol: usize| arities.get(symbol).copied();
            written.push((tree(left, arity)?, tree(right, arity)?));
        }
        stratum.symmetric.extend(system.symmetric);
        stratum.rules.extend(system.rules);
    }
    Some((stratum, written))
}

/// The verdict of item 1 on the decision `decided`.
///
/// # Specification
/// trivial.
fn convergence(decided: Result<(), gandr_kernel_term::OperationRuleRefusal>) -> &'static str
{
    match decided {
        Ok(()) => "joins",
        Err(refusal) => match refusal.fault {
            OperationRuleFault::Diverges(Overlapped::Presented { .. }) => {
                "parts at a mixed pair"
            },
            OperationRuleFault::Undecided(Overlapped::Presented { .. }) => {
                "undecided at a mixed pair"
            },
            OperationRuleFault::Diverges(_) | OperationRuleFault::Undecided(_) => {
                "parts at a pair of the operation"
            },
            OperationRuleFault::Unoriented => "unoriented",
            OperationRuleFault::Head
            | OperationRuleFault::NotAPattern
            | OperationRuleFault::Results
            | OperationRuleFault::UnknownConstructor
            | OperationRuleFault::UnknownOperation
            | OperationRuleFault::Arity
            | OperationRuleFault::NonLinear
            | OperationRuleFault::Unbound => "malformed",
        },
    }
}

/// The verdict of item 2 on the definition at `position`, by the replay's
/// first refusal `refused`.
///
/// # Specification
/// trivial.
fn replayed(
    position: usize,
    refused: Option<&(usize, KernelError)>,
) -> String
{
    match refused {
        None => String::from("admitted"),
        Some(&(at, _)) if position < at => String::from("admitted"),
        Some(&(at, _)) if position > at => String::from("not reached"),
        Some(&(_, KernelError::RuleNotRespected(_))) => String::from("breaks a rule of its type"),
        Some(&(_, KernelError::OperationRulesRefused(_))) => {
            String::from("refused by its convergence")
        },
        Some(&(_, ref error)) => {
            let shown = format!("{error:?}");
            let head = shown.split(['(', ' ', '{']).next().unwrap_or("");
            format!("refused: {head}")
        },
    }
}

/// The verdict of item 3 for the rules `own` of the operation over the lower
/// stratum `stratum`, at each mixed pair of `pairs`: each one as the rule
/// and the unifier.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `"unchanged"` when each pair is in the stratum, `"changes"`
///   when one is not, and `"undecided"` when a normal form takes more than
///   the steps of the oracle.
/// - panics: none.
///
/// # Cost
/// - allocation: the instances and their normal forms, growth within the
///   rules and the pairs
fn normalization(
    own: &[(Term, Term)],
    stratum: &System,
    pairs: &[(usize, super::Bindings)],
) -> &'static str
{
    for &(rule, ref bindings) in pairs {
        let Some(&(ref left, ref right)) = own.get(rule)
        else {
            return "undecided";
        };
        let instances = (resolved(left, bindings), resolved(right, bindings));
        let (Some(left), Some(right)) = instances
        else {
            return "undecided";
        };
        let normal = (stratum.normal_form(&left), stratum.normal_form(&right));
        let (Some(left), Some(right)) = normal
        else {
            return "undecided";
        };
        let in_stratum = own.iter().any(|&(ref other_left, ref other_right)| {
            matched(other_left, &left, &stratum.symmetric).is_some_and(|binding| {
                stratum.normal_form(&substituted(other_right, &binding)).as_ref() == Some(&right)
            })
        });
        if !in_stratum {
            return "changes";
        }
    }
    "unchanged"
}

/// The probe of the ruled definition at `position` of `declarations`; none
/// when its rules match no constructor of a presented type with rules, or a
/// side is no one term.
///
/// # Specification
/// - requires: `declarations` are one source's export, in order; `refused`
///   is the first refusal of their replay.
/// - ensures: the three verdicts of the module text, and the count of the
///   mixed pairs that item 1 forms: one for each rule of the operation, each
///   constructor below the root of its left side, and each rule of that
///   constructor's presentation, the symmetry included, whose left side
///   unifies with the pattern there.
/// - panics: none.
///
/// # Cost
/// - allocation: the terms of the rules, the unifiers and the normal forms,
///   growth within the rules of the operation and of its presented types
fn probe(
    declarations: &[MarkedDeclaration],
    position: usize,
    refused: Option<&(usize, KernelError)>,
) -> Option<Probe>
{
    let marked = declarations.get(position)?;
    let rules = marked.declaration().operation_rules();
    let scope = Below(declarations.get(.. position)?);
    let families = matched_families(rules, &scope);
    if families.is_empty() {
        return None;
    }
    let mut symbols = Symbols::default();
    let mut own = Vec::new();
    for rule in rules.rules() {
        let left = symbols.operation_side(rule.left(), &scope)?;
        let right = symbols.operation_side(rule.right(), &scope)?;
        own.push((left, right));
    }
    let (stratum, written) = lower(&families, &scope, &mut symbols)?;
    let arity = |symbol: usize| symbols.arities.get(symbol).copied();
    let own: Vec<(Term, Term)> = own
        .iter()
        .map(|&(ref left, ref right)| Some((tree(left, arity)?, tree(right, arity)?)))
        .collect::<Option<_>>()?;
    let constructors: BTreeSet<usize> = symbols
        .places
        .iter()
        .filter_map(|(&symbol, &place)| match symbol {
            Symbol::Constructor(family, _) if families.contains(&family) => Some(place),
            Symbol::Constructor(..) | Symbol::Operation(_) | Symbol::Results(_) => None,
        })
        .collect();
    let mut pairs = Vec::new();
    for (index, &(ref left, _)) in own.iter().enumerate() {
        for path in positions(left).into_iter().skip(1) {
            let Some(pattern @ &Term::Apply(symbol, _)) = at(left, &path)
            else {
                continue;
            };
            if !constructors.contains(&symbol) {
                continue;
            }
            for &(ref lower_left, _) in &written {
                let apart = |variable: u32| Term::Variable(variable.saturating_add(APART));
                let lower_left = rebuilt(lower_left, Term::Apply, apart);
                pairs.extend(
                    unifiers(pattern, &lower_left, &BTreeSet::new())
                        .into_iter()
                        .map(|bindings| (index, bindings)),
                );
            }
        }
    }
    let mut fuel = RewriteFuel::from(FUEL);
    let own_index = ConstantIndex::from(position);
    let decided = rules.converge((own_index, SourceRank::from(own_index)), &scope, &mut fuel);
    Some(Probe {
        name: named(marked.declaration()),
        mixed: pairs.len(),
        converge: convergence(decided),
        replay: replayed(position, refused),
        normalization: normalization(&own, &stratum, &pairs),
    })
}

/// The probe of each ruled definition of `declarations` over a presented
/// type with rules, with the kernel's replay of them over `arena`.
///
/// # Specification
/// trivial.
fn probes(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
) -> Vec<Probe>
{
    let refused = Environment::replay(arena.clone(), declarations)
        .err()
        .map(|refusal| (usize::from(refusal.position()), refusal.error().clone()));
    (0 .. declarations.len())
        .filter_map(|position| probe(declarations, position, refused.as_ref()))
        .collect()
}

/// The sweep of the probe and its record.
mod sweeps
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::fmt::Write as _;
    use std::path::Path;

    use gandr_surface_grammar::built_in;

    use super::super::admitted;
    use super::super::sources;
    use super::probes;

    /// A `data` block whose operation covers each constructor, beside the
    /// symmetry of its constructor of two fields.
    const BESIDE_A_SYMMETRY: &str = "data Bag : Type where {
  | Empty : Bag
  | Both : (x : Bag, y : Bag) --> Bag
  oper mirror : (b : Bag) --> Bag;
  rule : Both x y <=> Both y x;
  rule : mirror Empty ==> Empty;
  rule : mirror (Both x y) ==> Both (mirror y) (mirror x);
}
";

    /// The record: for each ruled definition over a presented type with
    /// rules, by its first source, its name, whether the check admits it,
    /// the count of its mixed pairs, and the verdicts of the three items of
    /// the module text.
    const RECORD: [(&str, &str, bool, usize, &str, &str, &str); 0] = [];

    /// Each ruled definition of the repository whose rules match a
    /// constructor of a presented type with rules, and the block of an
    /// operation beside a symmetry, by the three verdicts of the module
    /// text, as the record states.
    #[test]
    fn each_operation_over_a_presented_type_by_its_three_verdicts()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut texts = Vec::new();
        for root in ["corpus", "library", "crates"] {
            texts.extend(sources(&repository.join(root)));
        }
        texts.push((
            Path::new(env!("CARGO_MANIFEST_DIR")).join("operation-beside-a-symmetry.gandr"),
            String::from(BESIDE_A_SYMMETRY),
        ));
        let mut found: BTreeMap<(String, bool, usize, &str, String, &str), String> =
            BTreeMap::new();
        for &(ref path, ref text) in &texts {
            let Some(crossed) = admitted(&pbg, path, text)
            else {
                continue;
            };
            let shown = path
                .strip_prefix(&repository)
                .unwrap_or(path)
                .to_string_lossy()
                .into_owned();
            for probe in probes(&crossed.arena, &crossed.declarations) {
                let checked = crossed
                    .checked
                    .iter()
                    .any(|name| probe.name.ends_with(name.as_str()));
                let _first = found
                    .entry((
                        probe.name,
                        checked,
                        probe.mixed,
                        probe.converge,
                        probe.replay,
                        probe.normalization,
                    ))
                    .or_insert(shown.clone());
            }
        }
        let mut rows: Vec<(String, String, bool, usize, &str, String, &str)> = found
            .into_iter()
            .map(|((name, checked, mixed, converge, replay, normalization), source)| {
                (source, name, checked, mixed, converge, replay, normalization)
            })
            .collect();
        rows.sort();
        let matches = rows.len() == RECORD.len()
            && rows.iter().zip(RECORD).all(|(row, pinned)| {
                (
                    row.0.as_str(),
                    row.1.as_str(),
                    row.2,
                    row.3,
                    row.4,
                    row.5.as_str(),
                    row.6,
                ) == pinned
            });
        let mut table = String::new();
        for &(ref source, ref name, checked, mixed, converge, ref replay, normalization) in &rows {
            writeln!(
                table,
                "(\"{source}\", \"{name}\", {checked}, {mixed}, \"{converge}\", \"{replay}\", \"{normalization}\"),"
            )
            .expect("a string takes each write");
        }
        assert!(
            matches,
            "the ruled definitions over a presented type with rules differ from the record:\n{table}"
        );
    }
}
