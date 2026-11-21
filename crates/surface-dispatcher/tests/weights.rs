//! Probe 15 of the presented-spaces frame: a weight in the max-plus semiring
//! against the path order, on the corpus rule blocks.
//!
//! The lowering orients the rules of a block by the lexicographic path order,
//! and keeps the oriented rules in `DeclarationCells::oriented`. A weight
//! gives each constructor, operation, results tuple, binder and atom a natural
//! number. A term weighs the max-plus product of the weights of its symbols,
//! which is their sum. A rule decreases under a weight when its left side
//! outweighs its right side at every instance. Then each step lowers the
//! weight of the term by at least the least decrease of a rule. So the
//! weight of the start term, divided by that decrease, bounds the length of
//! each derivation.
//!
//! A rule decreases at every instance exactly when no variable occurs more
//! often on its right side, and the weights of its symbols fall. The probe
//! gives each block that the path order orients one verdict:
//!
//! |verdict|meaning|
//! |---|---|
//! |weighed|a weight within the budget decreases every rule|
//! |copies|the right side of a rule holds a variable more often than its left side, so an instance with a heavy term outweighs any fall|
//! |refuted|a combination of the rules with natural coefficients keeps or raises the count of every symbol, so no weight decreases all of them|
//! |second order|a rule instantiates a metavariable, whose weight is the weight of the term it stands for|
//! |undecided|neither search ends within the budget|
//!
//! Each search reads at most [`BUDGET`] candidates for a block.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::desc_cells::DeclarationCells;
use gandr_surface_syntax::SourceText;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermView;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::MaxPlus;
use gandr_theory_ordered_algebras::OrderedSemiring as _;
use gandr_theory_ordered_algebras::Tropical;

/// The most candidates one search reads for one block.
const BUDGET: u64 = 1 << 16;

/// A natural number: the weight of a symbol, or the coefficient of a rule.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct Natural(u64);

/// A signed count: the balance of a symbol or a variable between the two
/// sides of a rule, or the fall of a rule under a weight.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct Count(i64);

impl Count
{
    /// This count plus `other` times `scale`, saturating.
    ///
    /// # Specification
    /// trivial.
    fn add_scaled(
        self,
        other: Self,
        scale: Natural,
    ) -> Self
    {
        Self(
            self.0.saturating_add(
                other
                    .0
                    .saturating_mul(i64::try_from(scale.0).unwrap_or(i64::MAX)),
            ),
        )
    }
}

/// The side of a rule a term stands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side
{
    /// The left side, which counts up.
    Left,
    /// The right side, which counts down.
    Right,
}

/// A symbol a weight reads.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Symbol
{
    /// A constructor, by its name.
    Constructor(Name),
    /// An operation, by its name.
    Operation(Name),
    /// A results tuple.
    Results,
    /// A binder: an atom's abstraction or a binding field.
    Binder,
    /// An atom or a bound variable, named under its binder.
    Atom,
}

/// The balance of the symbols and variables of one rule: each count on the
/// left side less its count on the right.
#[derive(Debug, Default)]
struct Balance
{
    /// Each symbol's balance.
    symbols: BTreeMap<Symbol, Count>,
    /// Each pattern variable's balance.
    variables: BTreeMap<Name, Count>,
    /// Whether a side instantiates a metavariable.
    instantiates: bool,
}

impl Balance
{
    /// Count each symbol and each variable of `term`, standing on `side`.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &mut self,
        term: &FreeTerm,
        side: Side,
    )
    {
        let step = match side {
            Side::Left => Count(1),
            Side::Right => Count(-1),
        };
        let mut pending = vec![term.to_node()];
        while let Some(node) = pending.pop() {
            let symbol = match node.view() {
                TermView::Var(name) => {
                    let entry = self.variables.entry(name.clone()).or_default();
                    *entry = entry.add_scaled(step, Natural(1));
                    continue;
                },
                TermView::Inst { args, .. } => {
                    self.instantiates = true;
                    pending.extend(args);
                    continue;
                },
                TermView::Ctor { name, args } => {
                    pending.extend(args);
                    Symbol::Constructor(name.clone())
                },
                TermView::Op { name, args } => {
                    pending.extend(args);
                    Symbol::Operation(name.clone())
                },
                TermView::Results { args } => {
                    pending.extend(args);
                    Symbol::Results
                },
                TermView::Abs { args, .. } | TermView::Lam { args, .. } => {
                    pending.extend(args);
                    Symbol::Binder
                },
                TermView::Atom(_) | TermView::Bound(_) => Symbol::Atom,
            };
            let entry = self.symbols.entry(symbol).or_default();
            *entry = entry.add_scaled(step, Natural(1));
        }
    }

    /// Whether the right side holds some variable more often than the left.
    ///
    /// # Specification
    /// trivial.
    fn copies(&self) -> Copying
    {
        if self.variables.values().any(|balance| balance.0 < 0) {
            Copying::Copies
        }
        else {
            Copying::Keeps
        }
    }

    /// The fall of the rule under `weights`, one weight per symbol of
    /// `symbols`.
    ///
    /// # Specification
    /// trivial.
    fn fall(
        &self,
        symbols: &[&Symbol],
        weights: &[Natural],
    ) -> Count
    {
        symbols
            .iter()
            .zip(weights)
            .fold(Count::default(), |fall, (symbol, &weight)| {
                fall.add_scaled(
                    self.symbols.get(*symbol).copied().unwrap_or_default(),
                    weight,
                )
            })
    }
}

/// Whether a rule copies a variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Copying
{
    /// No variable occurs more often on the right side.
    Keeps,
    /// Some variable occurs more often on the right side.
    Copies,
}

/// How the probe reads one block.
#[derive(Debug)]
enum Verdict
{
    /// A weight within the budget decreases every rule by at least `least`.
    Weighed
    {
        /// The weight of each symbol whose count some rule changes.
        weights: BTreeMap<Symbol, Natural>,
        /// The least decrease of a rule.
        least: Count,
    },
    /// A rule copies a variable.
    Copies,
    /// A combination of the rules, one coefficient per rule, keeps or raises
    /// the count of every symbol.
    Refuted(Vec<Natural>),
    /// A rule instantiates a metavariable.
    SecondOrder,
    /// Neither search ends within the budget.
    Undecided,
}

/// One block's reading: where it is written, and its verdict.
#[derive(Debug)]
struct Row
{
    /// The source that writes the block.
    path: PathBuf,
    /// The first line of the block.
    header: String,
    /// The rules the path order orients.
    rules: usize,
    /// The verdict.
    verdict: Verdict,
}

/// The vectors of naturals of one length, each entry at most one bound, in
/// counting order.
#[derive(Debug)]
struct Candidates
{
    /// The next vector, or none past the last.
    next: Option<Vec<Natural>>,
    /// The bound on each entry.
    top: Natural,
}

impl Candidates
{
    /// The vectors of `length` entries, each at most the largest bound whose
    /// count of vectors fits [`BUDGET`]; none when even the bound one does
    /// not fit.
    ///
    /// # Specification
    /// trivial.
    fn within_budget(length: Length) -> Option<Self>
    {
        let fits = |top: u64| {
            u32::try_from(length.0)
                .ok()
                .and_then(|exponent| top.saturating_add(1).checked_pow(exponent))
                .is_some_and(|count| count <= BUDGET)
        };
        if !fits(1) {
            return None;
        }
        let mut top = 1_u64;
        while top < 8 && fits(top.saturating_add(1)) {
            top = top.saturating_add(1);
        }
        Some(Self {
            next: Some(vec![Natural::default(); length.0]),
            top: Natural(top),
        })
    }
}

impl Iterator for Candidates
{
    type Item = Vec<Natural>;

    /// The next vector in counting order.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<Vec<Natural>>
    {
        let current = self.next.take()?;
        let mut following = current.clone();
        for entry in &mut following {
            if *entry < self.top {
                *entry = Natural(entry.0.saturating_add(1));
                self.next = Some(following);
                return Some(current);
            }
            *entry = Natural::default();
        }
        Some(current)
    }
}

/// The number of entries of a candidate vector.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
struct Length(usize);

/// The oriented rules of `declaration`, as a weight reads them.
///
/// # Specification
/// trivial.
fn balances(declaration: &DeclarationCells) -> Vec<Balance>
{
    declaration
        .oriented
        .iter()
        .map(|face| {
            let mut balance = Balance::default();
            balance.add(&face.lhs, Side::Left);
            balance.add(&face.rhs, Side::Right);
            balance.symbols.retain(|_, count| count.0 != 0);
            balance
        })
        .collect()
}

/// The verdict on a block whose oriented rules are `rules`: second order
/// before copies, then a weight, then a refutation, then undecided.
///
/// # Specification
/// trivial.
fn decide(rules: &[Balance]) -> Verdict
{
    if rules.iter().any(|rule| rule.instantiates) {
        return Verdict::SecondOrder;
    }
    if rules.iter().any(|rule| rule.copies() == Copying::Copies) {
        return Verdict::Copies;
    }
    let mut symbols: Vec<&Symbol> = rules.iter().flat_map(|rule| rule.symbols.keys()).collect();
    symbols.sort();
    symbols.dedup();
    let weighed = Candidates::within_budget(Length(symbols.len())).and_then(|mut candidates| {
        candidates.find(|weights| {
            rules
                .iter()
                .all(|rule| rule.fall(&symbols, weights) >= Count(1))
        })
    });
    if let Some(weights) = weighed {
        let least = rules
            .iter()
            .map(|rule| rule.fall(&symbols, &weights))
            .min()
            .unwrap_or_default();
        return Verdict::Weighed {
            weights: symbols
                .iter()
                .map(|&symbol| symbol.clone())
                .zip(weights)
                .collect(),
            least,
        };
    }
    let refuted = Candidates::within_budget(Length(rules.len())).and_then(|mut candidates| {
        candidates.find(|coefficients| {
            coefficients
                .iter()
                .any(|&coefficient| coefficient > Natural(0))
                && symbols.iter().all(|symbol| {
                    rules.iter().zip(coefficients).fold(
                        Count::default(),
                        |total, (rule, &coefficient)| {
                            total.add_scaled(
                                rule.symbols.get(*symbol).copied().unwrap_or_default(),
                                coefficient,
                            )
                        },
                    ) <= Count(0)
                })
        })
    });
    refuted.map_or(Verdict::Undecided, Verdict::Refuted)
}

/// The weight of `term` in the max-plus semiring: the product of the weights
/// of its symbols, a variable and a symbol `weights` leaves out weighing the
/// unit.
///
/// # Specification
/// trivial.
fn weight(
    term: &FreeTerm,
    weights: &BTreeMap<Symbol, Natural>,
) -> MaxPlus
{
    let semiring = Tropical::default();
    let mut balance = Balance::default();
    balance.add(term, Side::Left);
    balance
        .symbols
        .iter()
        .flat_map(|(symbol, &occurrences)| {
            let each = weights.get(symbol).copied().unwrap_or_default();
            core::iter::repeat_n(each, usize::try_from(occurrences.0).unwrap_or(0))
        })
        .fold(semiring.one(), |product, each| {
            let factor = MaxPlus::Finite(Dyadic::from(i64::try_from(each.0).unwrap_or(i64::MAX)));
            semiring
                .multiply(&product, &factor)
                .expect("a weight within the budget stays exact")
        })
}

/// The verdict on every corpus block that the path order orients, in path
/// order and then in written order, each weight and each refutation checked
/// on its own.
///
/// # Specification
/// trivial.
fn probe() -> Vec<Row>
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let mut rows = Vec::new();
    for path in super::coincide::sources() {
        let text = std::fs::read_to_string(&path).expect("the source reads");
        if !text.contains("rule ") {
            continue;
        }
        let Lowered::Module { module, .. } =
            lower_source(&grammar, SourceText::from(text.as_str()), &mut lowerings)
                .unwrap_or_else(|fault| panic!("{}: {fault}", path.display()))
                .into_lowered()
        else {
            continue;
        };
        for declaration in &module.cells().declarations {
            if declaration.oriented.is_empty() {
                continue;
            }
            let span = declaration.at.span;
            let header = text
                .get(usize::from(span.start()) .. usize::from(span.end()))
                .and_then(|written| written.lines().next())
                .unwrap_or_default()
                .into();
            let read = balances(declaration);
            let verdict = decide(&read);
            match verdict {
                Verdict::Weighed { ref weights, least } => {
                    assert!(least >= Count(1), "{}: each rule falls", path.display());
                    let semiring = Tropical::default();
                    for face in &declaration.oriented {
                        assert_eq!(
                            semiring
                                .compare(&weight(&face.lhs, weights), &weight(&face.rhs, weights)),
                            Comparison::NotBelow,
                            "{}: a weighed rule's left side outweighs its right side",
                            path.display()
                        );
                    }
                },
                Verdict::Refuted(ref coefficients) => {
                    let mut combined: BTreeMap<&Symbol, Count> = BTreeMap::new();
                    for (rule, &coefficient) in read.iter().zip(coefficients) {
                        for (symbol, &balance) in &rule.symbols {
                            let entry = combined.entry(symbol).or_default();
                            *entry = entry.add_scaled(balance, coefficient);
                        }
                    }
                    assert!(
                        coefficients
                            .iter()
                            .any(|&coefficient| coefficient > Natural(0))
                            && combined.values().all(|&total| total <= Count(0)),
                        "{}: a refutation keeps or raises the count of every symbol",
                        path.display()
                    );
                },
                Verdict::Copies | Verdict::SecondOrder | Verdict::Undecided => {},
            }
            rows.push(Row {
                path: path.clone(),
                header,
                rules: read.len(),
                verdict,
            });
        }
    }
    rows
}

/// A block of the corpus: the path of its source below the corpus, and its
/// first line.
#[derive(Clone, Copy, Debug)]
struct Block<'block>
{
    /// The source's path below the corpus.
    source: &'block Path,
    /// The block's first line.
    header: &'block str,
}

/// The verdict on `block`.
///
/// # Specification
/// trivial.
fn verdict<'rows>(
    rows: &'rows [Row],
    block: Block<'_>,
) -> &'rows Verdict
{
    let mut matched = rows
        .iter()
        .filter(|row| row.path.ends_with(block.source) && row.header == block.header);
    let row = matched
        .next()
        .unwrap_or_else(|| panic!("{block:?}: no such block"));
    assert!(matched.next().is_none(), "{block:?}: one block");
    &row.verdict
}

#[test]
fn the_path_order_orients_blocks_that_no_weight_decreases()
{
    let rows = probe();
    let block = |source: &'static str, header: &'static str| Block {
        source: Path::new(source),
        header,
    };
    // Every block the order orients takes a verdict within the budget.
    assert!(
        rows.iter()
            .all(|row| row.rules > 0 && !matches!(row.verdict, Verdict::Undecided)),
        "a block passes the budget: {rows:?}"
    );
    // An involution falls by two under the weight one for its operation.
    assert!(matches!(
        verdict(&rows, block("model/modules/model-ascription.gandr", "theory Toggle where")),
        &Verdict::Weighed { ref weights, least: Count(2) } if weights.values().eq([&Natural(1)])
    ));
    // Associativity keeps the count of every symbol, so no weight decreases
    // it, and the order orients it all the same.
    assert!(matches!(
        verdict(&rows, block("model/include/monoid.gandr", "theory Semigroup where")),
        Verdict::Refuted(coefficients) if coefficients == &[Natural(1)]
    ));
    // A rule that copies a variable, and a rule that instantiates a
    // metavariable, take their own verdicts.
    assert!(matches!(
        verdict(
            &rows,
            block("model/data/map-laws.gandr", "theory ListMap where")
        ),
        Verdict::Copies
    ));
    assert!(matches!(
        verdict(
            &rows,
            block("model/desc/second-order-rules.gandr", "theory Let where")
        ),
        Verdict::SecondOrder
    ));
}
