//! Probe 1 of the presented-spaces frame, run where the frame places it.
//!
//! The frame reads completion's critical pairs as the critical cells of a
//! collapse of the standard resolution. For a block whose operations are all
//! unary, the rules are a string rewriting system, and the block presents a
//! monoid. The standard resolution of a monoid is its bar complex. Its cells
//! are the tuples of nonempty normal forms. The suite reads such a block as
//! the Lawvere theory of its letters, whose cells in one variable are the
//! cells of that bar complex. Brown's collapsing scheme, along the rules,
//! pairs every other cell and leaves Anick's chains: the letters, the rules'
//! left sides, and the chains of overlaps of two left sides. The suite builds
//! the bar complex of each such block of the corpus, truncated at a word
//! length, collapses it through the scheme of `theory-coherent-resolutions`,
//! and compares the chains of dimensions two, three and four with the rules,
//! the pairs that completion certifies and the critical triples of the block's
//! cells.
//!
//! The suite also computes Squier's homology over the rationals on the small
//! complex of every block of the corpus: one cell for each symbol, each rule
//! and each certified pair. A rule's boundary counts the symbols of its left
//! side less those of its right side. A pair's boundary counts the rules along
//! its first joining path less those along its second.
//!
//! The suite also reads `IntOp`, the one block whose rule defines a letter,
//! as Tietze moves. The bar complex holds no cell of that letter, because the
//! letter is no normal form. Its drop is one move on the written presentation,
//! and Brown's critical cells spell what that move leaves. Through integer
//! chains, each removal of Brown's scheme, matched alone, is an equivalence
//! that replays, and the removals compose to the scheme's collapse.
//!
//! A block with a binary operation is the concern of the collapse suite,
//! which reads the bar complex of its Lawvere theory.
//!
//! # References
//!
//! - `Ara-2025-polygraphs_rewriting_higher_categories` — newest: the critical
//!   branchings of a convergent polygraph give its coherence cells, and
//!   Squier's homology counts them.
//! - `Malbos-2021-completion_operads_essential_syzygies` — newest: completion
//!   adds the cells of a resolution, and the essential ones are the pairs.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::convert::Infallible;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_term::CoreArena;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::coincide::Certificates;
use gandr_surface_lowering::coincide::Coincidence;
use gandr_surface_lowering::desc_cells::DeclarationCells;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_coherent_resolutions::Arity;
use gandr_theory_coherent_resolutions::Arrow;
use gandr_theory_coherent_resolutions::BarCell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::LawvereTheory;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_coherent_resolutions::critical_triples;
use gandr_theory_computads::EtaElaboration;
use gandr_theory_computads::Term;
use gandr_theory_discrete_morse::Abelian;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Chain;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Composites as _;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Invertibility;
use gandr_theory_discrete_morse::Reduction as _;
use gandr_theory_discrete_morse::Scheme;
use gandr_theory_discrete_morse::Standing;
use gandr_theory_discrete_morse::equivalence;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

/// The longest word the bar complex of a unary block holds, in letters.
const WORD_BUDGET: usize = 6;

/// A letter of a unary block: the place of a unary symbol in its alphabet.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Letter(u8);

/// A word over a unary block's letters, the outermost symbol first.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Word(Vec<Letter>);

impl Word
{
    /// The word `self` then `other`.
    ///
    /// # Specification
    /// trivial.
    fn then(
        &self,
        other: &Self,
    ) -> Self
    {
        let mut joined = self.0.clone();
        joined.extend_from_slice(&other.0);
        Self(joined)
    }
}

/// Whether a word holds the left side of a rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reducibility
{
    /// The word holds a left side.
    Reducible,
    /// The word is a normal form.
    Irreducible,
}

/// A unary block's rules as a string rewriting system.
#[repr(transparent)]
#[derive(Debug)]
struct Strings
{
    /// The rules, each left side then right side.
    rules: Vec<(Word, Word)>,
}

impl Strings
{
    /// Whether `word` holds a left side.
    ///
    /// # Specification
    /// trivial.
    fn reducibility(
        &self,
        word: &Word,
    ) -> Reducibility
    {
        if self.rules.iter().any(|&(ref left, _)| {
            word.0
                .windows(left.0.len().max(1))
                .any(|window| window == left.0.as_slice())
        }) {
            Reducibility::Reducible
        }
        else {
            Reducibility::Irreducible
        }
    }

    /// The longest left side that ends `word`.
    ///
    /// # Specification
    /// trivial.
    fn ending(
        &self,
        word: &Word,
    ) -> Word
    {
        self.rules
            .iter()
            .map(|&(ref left, _)| left)
            .filter(|left| word.0.ends_with(&left.0))
            .max_by_key(|left| left.0.len())
            .expect("a chain ends with a left side")
            .clone()
    }
}

/// A coefficient of a boundary.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Coefficient(i64);

/// The Lawvere theory of `strings` over `letters` letters: each letter a unary
/// operation, and each word of a rule the term it spells in the variable `x₁`.
///
/// # Specification
/// trivial.
fn theory(
    strings: &Strings,
    letters: LetterCount,
) -> LawvereTheory
{
    let mut table = TermTable::default();
    let rules = strings
        .rules
        .iter()
        .map(|&(ref left, ref right)| (spelt(&mut table, left), spelt(&mut table, right)))
        .collect();
    let arities = vec![Arity::from(1_usize); usize::from(letters.0)];
    LawvereTheory::new(
        arities,
        rules,
        table,
        NormalizationBudget::from(1_000_usize),
    )
    .expect("each word of a rule holds its variable once")
}

/// The term that `word` spells in the variable `x₁`, the outermost letter
/// first.
///
/// # Specification
/// trivial.
fn spelt(
    table: &mut TermTable,
    word: &Word,
) -> TermPlace
{
    let mut place = table.var(Variable::from(0_usize));
    for letter in word.0.iter().rev() {
        place = table
            .op(Operation::from(usize::from(letter.0)), vec![place])
            .expect("a letter takes a term of the table");
    }
    place
}

/// The cell of the bar complex whose arrows the words `entries` spell, each
/// in one variable.
///
/// # Specification
/// trivial.
fn bar_cell(
    table: &mut TermTable,
    entries: &[Word],
) -> BarCell
{
    BarCell(
        entries
            .iter()
            .map(|word| Arrow {
                source: Arity::from(1_usize),
                terms: vec![spelt(table, word)],
            })
            .collect(),
    )
}

/// The words that the arrows of `cell` spell, or none for an arrow that is no
/// chain of letters over one variable.
///
/// # Specification
/// trivial.
fn entries(
    table: &TermTable,
    cell: &BarCell,
) -> Option<Vec<Word>>
{
    let mut out = Vec::with_capacity(cell.0.len());
    for arrow in &cell.0 {
        let [mut place] = *arrow.terms.as_slice()
        else {
            return None;
        };
        let mut letters = Vec::new();
        loop {
            let node = table.node(place).ok()?;
            match node.head {
                TermHead::Var(_) => break,
                TermHead::Op(operation) => {
                    letters.push(Letter(u8::try_from(usize::from(operation)).ok()?));
                    let [inner] = *node.children.as_slice()
                    else {
                        return None;
                    };
                    place = inner;
                },
            }
        }
        out.push(Word(letters));
    }
    Some(out)
}

/// Every tuple of nonempty normal forms of `strings` over `letters` letters,
/// its entries' lengths summing to at most [`WORD_BUDGET`], by dimension.
///
/// # Specification
/// trivial.
fn bar_cells(
    strings: &Strings,
    letters: LetterCount,
) -> Vec<Vec<Vec<Word>>>
{
    let mut normal: Vec<Word> = Vec::new();
    let mut layer: Vec<Word> = vec![Word::default()];
    for _ in 0 .. WORD_BUDGET {
        let mut next = Vec::with_capacity(layer.len().saturating_mul(usize::from(letters.0)));
        for word in &layer {
            for letter in 0 .. letters.0 {
                let mut grown = word.0.clone();
                grown.push(Letter(letter));
                let grown = Word(grown);
                if strings.reducibility(&grown) == Reducibility::Irreducible {
                    next.push(grown);
                }
            }
        }
        normal.extend(next.iter().cloned());
        layer = next;
    }
    let mut by_dimension: Vec<Vec<Vec<Word>>> = vec![vec![Vec::new()]];
    loop {
        let last = by_dimension.last().expect("the empty cell");
        let mut next = Vec::new();
        for cell in last {
            let used: usize = cell.iter().map(|word| word.0.len()).sum();
            for word in &normal {
                if used.saturating_add(word.0.len()) <= WORD_BUDGET {
                    let mut grown = cell.clone();
                    grown.push(word.clone());
                    next.push(grown);
                }
            }
        }
        if next.is_empty() {
            return by_dimension;
        }
        by_dimension.push(next);
    }
}

/// The number of letters of a unary block's alphabet.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LetterCount(u8);

/// The word a free term spells when each node down to one variable is a unary
/// symbol, outermost first, with that variable; otherwise none.
///
/// # Specification
/// trivial.
fn chain(term: &FreeTerm) -> Option<(Vec<String>, String)>
{
    let mut letters = Vec::new();
    let mut view: TermView<'_> = term.view();
    loop {
        match view {
            TermView::Var(name) => return Some((letters, String::from(name.as_ref()))),
            TermView::Ctor { name, mut args } | TermView::Op { name, mut args }
                if args.len() == 1 =>
            {
                letters.push(String::from(name.as_ref()));
                let inner: TermNode<'_> = args.next()?;
                view = inner.view();
            },
            TermView::Ctor { .. }
            | TermView::Op { .. }
            | TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => return None,
        }
    }
}

/// The occurrences of each symbol in a free term, or none for a term that
/// binds or instantiates.
///
/// # Specification
/// trivial.
fn symbols(term: &FreeTerm) -> Option<BTreeMap<String, Coefficient>>
{
    let mut counts: BTreeMap<String, Coefficient> = BTreeMap::new();
    let mut pending: Vec<TermView<'_>> = vec![term.view()];
    while let Some(view) = pending.pop() {
        match view {
            TermView::Var(_) => {},
            TermView::Ctor { name, args } | TermView::Op { name, args } => {
                let count = counts.entry(String::from(name.as_ref())).or_default();
                count.0 = count.0.saturating_add(1);
                pending.extend(args.map(TermNode::view));
            },
            TermView::Results { args } => pending.extend(args.map(TermNode::view)),
            TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => return None,
        }
    }
    Some(counts)
}

/// The free term a stored term spells.
///
/// # Specification
/// trivial.
pub fn spelled(term: &Term) -> Option<FreeTerm>
{
    match term.read() {
        Maybe::Present(free) => Some(free),
        Maybe::Absent(_) => None,
    }
}

/// The reading a block's pairs are decided in.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Reading
{
    /// The sequent reading, over commands.
    Commands,
    /// The presented reading, over terms.
    Terms,
}

/// The small complex of one reading of a block: its symbols, each rule's
/// boundary over them, and each certified pair's boundary over the rules.
#[derive(Debug, Default)]
pub struct Small
{
    /// The symbols, in order.
    symbols: Vec<String>,
    /// Each rule's boundary: the symbols of its left side less those of its
    /// right side.
    rules: Vec<Vec<Coefficient>>,
    /// Each pair's boundary: the rules along its first path less those along
    /// its second.
    pairs: Vec<Vec<Coefficient>>,
}

/// The dimensions of the homology of a small complex, the last an upper
/// bound, since no cell of dimension three is built.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Homology
{
    /// Symbols less the rank of the rules' boundary.
    pub first: Rank,
    /// The rules' cycles less the rank of the pairs' boundary.
    pub second: Rank,
    /// The pairs' cycles: an upper bound on the third homology.
    pub third_at_most: Rank,
}

/// A rank or a dimension.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Rank(pub usize);

/// The rank over the rationals of the matrix whose columns are `columns`,
/// each of `rows` entries, by fraction-free elimination.
///
/// # Specification
/// trivial.
fn rank(
    columns: &[Vec<Coefficient>],
    rows: Rank,
) -> Rank
{
    let mut matrix: Vec<Vec<i128>> = (0 .. rows.0)
        .map(|row| {
            columns
                .iter()
                .map(|column| i128::from(column.get(row).copied().unwrap_or_default().0))
                .collect()
        })
        .collect();
    let width = columns.len();
    let mut found = 0_usize;
    let mut previous: i128 = 1;
    for column in 0 .. width {
        let Some(pivot) = (found .. rows.0).find(|&row| matrix[row][column] != 0)
        else {
            continue;
        };
        matrix.swap(found, pivot);
        for row in found.saturating_add(1) .. rows.0 {
            for other in column.saturating_add(1) .. width {
                let value = matrix[found][column]
                    .checked_mul(matrix[row][other])
                    .and_then(|kept| {
                        kept.checked_sub(matrix[row][column].checked_mul(matrix[found][other])?)
                    })
                    .and_then(|value| value.checked_div(previous))
                    .expect("the entries of a small complex stay small");
                matrix[row][other] = value;
            }
            matrix[row][column] = 0;
        }
        previous = matrix[found][column];
        found = found.saturating_add(1);
    }
    Rank(found)
}

impl Small
{
    /// The homology's dimensions.
    ///
    /// # Specification
    /// trivial.
    pub fn homology(&self) -> Option<Homology>
    {
        if self.closed() == Reducibility::Reducible {
            return None;
        }
        let rules = rank(&self.rules, Rank(self.symbols.len()));
        let pairs = rank(&self.pairs, Rank(self.rules.len()));
        Some(Homology {
            first: Rank(self.symbols.len().checked_sub(rules.0)?),
            second: Rank(
                self.rules
                    .len()
                    .checked_sub(rules.0)?
                    .checked_sub(pairs.0)?,
            ),
            third_at_most: Rank(self.pairs.len().checked_sub(pairs.0)?),
        })
    }

    /// Whether the boundary of each pair's boundary is zero: the two joining
    /// paths of each pair change the symbols alike.
    ///
    /// # Specification
    /// trivial.
    fn closed(&self) -> Reducibility
    {
        for pair in &self.pairs {
            for symbol in 0 .. self.symbols.len() {
                let total = pair
                    .iter()
                    .zip(&self.rules)
                    .map(|(along, rule)| {
                        along
                            .0
                            .saturating_mul(rule.get(symbol).copied().unwrap_or_default().0)
                    })
                    .fold(0_i64, i64::saturating_add);
                if total != 0 {
                    return Reducibility::Reducible;
                }
            }
        }
        Reducibility::Irreducible
    }
}

/// The small complex of `rules` and `pairs`, each pair's path steps read
/// through `index`. A step that fires a cell of `structural`, a frame cell of
/// the sequent reading, leaves the term's symbols alone and counts for no
/// rule. An eta cell changes them, so a step that fires one is unread. None
/// when a rule is not first-order or a step fires a cell neither names.
///
/// # Specification
/// trivial.
fn small<A>(
    rules: &[(FreeTerm, FreeTerm)],
    (index, structural): (&BTreeMap<CellId, RuleIndex>, &BTreeSet<CellId>),
    pairs: &[Tracelet<A>],
) -> Option<Small>
where
    A: gandr_theory_cell_complexes::CellAlphabet,
{
    let mut counted = Vec::with_capacity(rules.len());
    let mut names: BTreeSet<String> = BTreeSet::new();
    for &(ref left, ref right) in rules {
        let (left, right) = (symbols(left)?, symbols(right)?);
        names.extend(left.keys().cloned());
        names.extend(right.keys().cloned());
        counted.push((left, right));
    }
    let symbols: Vec<String> = names.into_iter().collect();
    let rules = counted
        .iter()
        .map(|&(ref left, ref right)| {
            symbols
                .iter()
                .map(|symbol| {
                    Coefficient(
                        left.get(symbol)
                            .copied()
                            .unwrap_or_default()
                            .0
                            .saturating_sub(right.get(symbol).copied().unwrap_or_default().0),
                    )
                })
                .collect()
        })
        .collect::<Vec<Vec<Coefficient>>>();
    let along = |path: &[CellApp<A>], sign: i64, column: &mut Vec<Coefficient>| -> Option<()> {
        for step in path {
            if structural.contains(&step.cell) {
                continue;
            }
            let rule = index.get(&step.cell)?;
            let entry = column.get_mut(rule.0)?;
            entry.0 = entry.0.saturating_add(sign);
        }
        Some(())
    };
    let mut columns = Vec::with_capacity(pairs.len());
    for pair in pairs {
        let mut column = vec![Coefficient::default(); rules.len()];
        along(&pair.path_a, 1, &mut column)?;
        along(&pair.path_b, -1, &mut column)?;
        columns.push(column);
    }
    Some(Small {
        symbols,
        rules,
        pairs: columns,
    })
}

/// The place of a rule in a block's small complex.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RuleIndex(pub usize);

/// What Brown's collapsing scheme leaves on a unary block: the essential cells
/// of dimension two as words, those of dimension three as their peak and their
/// two left sides, and those of dimension four as their peak and their three
/// left sides, each from the start of the peak.
#[derive(Debug, Default, Eq, PartialEq)]
struct Collapse
{
    /// The words of the essential cells of dimension two.
    rules: BTreeSet<Word>,
    /// The peak and the two left sides of each essential cell of dimension
    /// three.
    pairs: BTreeSet<(Word, Word, Word)>,
    /// The peak and the three left sides of each essential cell of dimension
    /// four.
    triples: BTreeSet<(Word, Word, Word, Word)>,
}

/// Collapse the bar complex of `strings` through Brown's collapsing scheme of
/// its Lawvere theory. The Morse crate checks that the scheme is an acyclic
/// matching: each pair's partner names it back, the redundant cell has the
/// incidence one or minus one in its partner's boundary, and the gradient has
/// no cycle.
///
/// # Specification
/// trivial.
fn collapse(
    strings: &Strings,
    letters: LetterCount,
) -> Collapse
{
    let mut theory = theory(strings, letters);
    let by_dimension: Vec<Vec<BarCell>> = bar_cells(strings, letters)
        .iter()
        .map(|cells| {
            cells
                .iter()
                .map(|words| bar_cell(theory.table_mut(), words))
                .collect()
        })
        .collect();
    // A partner keeps the letters of its cell, so the walk stays inside the
    // truncation and visits fewer cells than it holds.
    let held = by_dimension
        .iter()
        .map(Vec::len)
        .fold(0_usize, usize::saturating_add);
    let done = gandr_theory_discrete_morse::collapse(
        &mut theory,
        by_dimension.iter().flatten(),
        Budget::from(held),
    )
    .expect("the walk stays inside the truncation");
    assert_eq!(
        done.faults(),
        Faults::default(),
        "Brown's scheme is an acyclic matching"
    );
    let mut out = Collapse::default();
    for cell in done.critical() {
        let words = entries(theory.table(), cell).expect("a cell of a unary block spells words");
        match *words.as_slice() {
            [ref x, ref u] => {
                let _new = out.rules.insert(x.then(u));
            },
            [ref x, ref u, ref v] => {
                let peak = x.then(u).then(v);
                let _new = out
                    .pairs
                    .insert((peak, x.then(u), strings.ending(&u.then(v))));
            },
            [ref x, ref u, ref v, ref w] => {
                let peak = x.then(u).then(v).then(w);
                let _new = out.triples.insert((
                    peak,
                    x.then(u),
                    strings.ending(&u.then(v)),
                    strings.ending(&u.then(v).then(w)),
                ));
            },
            _ => {},
        }
    }
    out
}

/// How a corpus source lowered.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Lowering
{
    /// The parser refused the source.
    Unparsed,
    /// The lowering refused the source as a whole.
    Refused,
    /// The lowering read the source's declarations.
    Lowered,
}

/// Lower `source` and hand each block's cells to `visit`.
///
/// # Specification
/// trivial.
pub fn each_block<Visit>(
    grammar: &Pbg,
    source: SourceText<'_>,
    mut visit: Visit,
) -> Lowering
where
    Visit: FnMut(&DeclarationCells),
{
    let Ok(parsed) = parse(grammar, source)
    else {
        return Lowering::Unparsed;
    };
    let tree = parsed.into_tree();
    let mut arena = CoreArena::new();
    let Ok(module) = lower_module(
        grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    else {
        return Lowering::Refused;
    };
    for cells in &module.cells().declarations {
        visit(cells);
    }
    Lowering::Lowered
}

/// The certificates of a block whose rules joined, none for an orthogonal
/// block, or nothing for a block the check refused or did not examine.
///
/// # Specification
/// trivial.
pub fn certified(cells: &DeclarationCells) -> Option<Certificates>
{
    match cells.coincidence {
        Coincidence::Joined(ref certificates) => Some(certificates.clone()),
        Coincidence::Orthogonal => Some(Certificates::default()),
        Coincidence::Unexamined | Coincidence::Refused(_) => None,
    }
}

/// A unary block read as strings: its rules, its letter count, the certified
/// pairs of its presented reading as their peak and two left sides, and the
/// critical triples of its presented cells as their peak and three left sides.
struct UnaryBlock
{
    /// The rules as a string rewriting system.
    strings: Strings,
    /// The number of letters.
    letters: LetterCount,
    /// The certified pairs.
    certified: BTreeSet<(Word, Word, Word)>,
    /// The critical triples, each left side in the order of the peak.
    triples: BTreeSet<(Word, Word, Word, Word)>,
}

/// The block `cells` read as strings when its presented reading's rules are
/// all chains of unary symbols over one variable, and its rules joined.
///
/// # Specification
/// trivial.
fn unary(cells: &DeclarationCells) -> Option<UnaryBlock>
{
    let Maybe::Present(ref presented) = cells.presented
    else {
        return None;
    };
    let certificates = certified(cells)?;
    let mut spelled_rules: Vec<(CellId, Vec<String>, Vec<String>)> = Vec::new();
    for (id, cell) in presented.store.iter() {
        let (left, left_variable) = chain(&spelled(cell.lhs())?)?;
        let (right, right_variable) = chain(&spelled(cell.rhs())?)?;
        if left.is_empty() || left_variable != right_variable {
            return None;
        }
        spelled_rules.push((id, left, right));
    }
    let names: BTreeSet<&String> = spelled_rules
        .iter()
        .flat_map(|&(_, ref left, ref right)| left.iter().chain(right))
        .collect();
    let names: Vec<&String> = names.into_iter().collect();
    let word = |letters: &[String]| {
        Word(
            letters
                .iter()
                .map(|name| {
                    let place = names.binary_search(&name).expect("a letter of the block");
                    Letter(u8::try_from(place).expect("a small alphabet"))
                })
                .collect(),
        )
    };
    let mut left_of: BTreeMap<CellId, Word> = BTreeMap::new();
    let mut rules = Vec::with_capacity(spelled_rules.len());
    for &(id, ref left, ref right) in &spelled_rules {
        let _previous = left_of.insert(id, word(left));
        rules.push((word(left), word(right)));
    }
    let mut pairs = BTreeSet::new();
    for pair in &certificates.terms {
        let (peak, _) = chain(&spelled(&pair.overlap.peak)?)?;
        let _new = pairs.insert((
            word(&peak),
            left_of.get(&pair.overlap.left)?.clone(),
            left_of.get(&pair.overlap.right)?.clone(),
        ));
    }
    let mut triples = BTreeSet::new();
    for triple in critical_triples(&presented.store) {
        let (peak, _) = chain(&spelled(&triple.peak)?)?;
        let [ref first, ref second, ref third] = triple.steps;
        let _new = triples.insert((
            word(&peak),
            left_of.get(&first.cell)?.clone(),
            left_of.get(&second.cell)?.clone(),
            left_of.get(&third.cell)?.clone(),
        ));
    }
    Some(UnaryBlock {
        strings: Strings { rules },
        letters: LetterCount(u8::try_from(names.len()).expect("a small alphabet")),
        certified: pairs,
        triples,
    })
}

/// One reading's rules, read through the cells its pairs fire.
#[derive(Debug, Default)]
pub struct Presentation
{
    /// The rules, each left side then right side.
    pub rules: Vec<(FreeTerm, FreeTerm)>,
    /// The rule that each cell fires.
    pub index: BTreeMap<CellId, RuleIndex>,
    /// The frame cells. Each moves a command and keeps the term, so it fires
    /// no rule.
    pub structural: BTreeSet<CellId>,
}

/// The rules of each reading of `cells` that holds rules, or none for a
/// reading whose rules do not all spell free terms.
///
/// # Specification
/// trivial.
pub fn readings(
    cells: &DeclarationCells,
    certificates: &Certificates,
) -> Vec<(Reading, Option<Presentation>)>
{
    let mut out = Vec::new();
    if let Maybe::Present(ref presented) = cells.presented {
        let mut read = Presentation::default();
        let mut readable = true;
        for (place, (id, cell)) in presented.store.iter().enumerate() {
            match (spelled(cell.lhs()), spelled(cell.rhs())) {
                (Some(left), Some(right)) => read.rules.push((left, right)),
                _ => readable = false,
            }
            let _previous = read.index.insert(id, RuleIndex(place));
        }
        out.push((Reading::Terms, readable.then_some(read)));
    }
    if !cells.faces.is_empty() {
        // The pairs' paths fire cells of the rewriting store, which keeps the
        // admitted faces' cells in a store of its own, so each of its cells
        // is read through the equal cell of the declaration's store.
        let rewriting = cells.rewriting();
        let mut read = Presentation::default();
        let eta: BTreeSet<CellId> = match cells.eta {
            EtaElaboration::Minted(ref minted) => minted.iter().copied().collect(),
            EtaElaboration::Declined(_) => BTreeSet::new(),
        };
        let faces: BTreeMap<CellId, usize> = cells
            .faces
            .iter()
            .map(|&(face, held)| (held, usize::from(face)))
            .collect();
        for (id, cell) in rewriting.iter() {
            let stored = cells
                .store
                .iter()
                .find(|&(_, held)| held == cell)
                .map(|(stored, _)| stored);
            let face = stored
                .and_then(|stored| faces.get(&stored))
                .and_then(|&face| cells.oriented.get(face));
            if let Some(rule) = face {
                let _previous = read.index.insert(id, RuleIndex(read.rules.len()));
                read.rules.push((rule.lhs.clone(), rule.rhs.clone()));
            }
            else if stored.is_some_and(|stored| !eta.contains(&stored)) {
                // A frame cell: it moves a command and keeps the term.
                let _new = read.structural.insert(id);
            }
        }
        for derived in &certificates.derived_commands {
            let _was_structural = read.structural.remove(&derived.cell);
            let _previous = read.index.insert(derived.cell, RuleIndex(read.rules.len()));
            read.rules.push(derived.rule.clone());
        }
        out.push((Reading::Commands, Some(read)));
    }
    out
}

/// The small complex of each reading of `cells` that holds rules, or none for
/// a reading the small complex cannot read.
///
/// # Specification
/// trivial.
pub fn small_complexes(cells: &DeclarationCells) -> Vec<(Reading, Option<Small>)>
{
    let Some(certificates) = certified(cells)
    else {
        return Vec::new();
    };
    readings(cells, &certificates)
        .into_iter()
        .map(|(reading, rules)| {
            let complex = rules.and_then(|read| {
                let cells = (&read.index, &read.structural);
                match reading {
                    Reading::Terms => small(&read.rules, cells, &certificates.terms),
                    Reading::Commands => small(&read.rules, cells, &certificates.commands),
                }
            });
            (reading, complex)
        })
        .collect()
}

/// Every corpus source, by path, in path order.
///
/// # Specification
/// trivial.
pub fn corpus() -> Vec<PathBuf>
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let mut pending = vec![root];
    let mut found = Vec::new();
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(&directory).expect("a corpus directory reads") {
            let path = entry.expect("a corpus entry reads").path();
            if path.is_dir() {
                pending.push(path);
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// The circle presented by its two cancellations.
const CIRCLE: &str = include_str!("squier/fixtures/circle.gandr");

#[test]
fn the_circles_bar_complex_collapses_onto_its_two_rules_pairs_and_triples()
{
    // The letters are `Loop` and `Unloop`, in name order. Brown's scheme keeps
    // `[Loop|Unloop]` and `[Unloop|Loop]`, the two left sides, and
    // `[Loop|Unloop|Loop]` and `[Unloop|Loop|Unloop]`, the two overlaps.
    // Completion certifies the same two overlaps. It also keeps
    // `[Loop|Unloop|Loop|Unloop]` and `[Unloop|Loop|Unloop|Loop]`, the two
    // critical triples. The outer two left sides of each share no letter.
    let grammar = built_in().expect("the built-in grammar builds");
    let mut blocks = Vec::new();
    let lowering = each_block(&grammar, SourceText::from(CIRCLE), |cells| {
        blocks.push(unary(cells).expect("the circle is a unary block"));
    });
    assert_eq!(lowering, Lowering::Lowered);
    let [ref block] = *blocks.as_slice()
    else {
        panic!("one block");
    };
    let (looped, unlooped) = (Letter(0), Letter(1));
    let word = |letters: &[Letter]| Word(letters.to_vec());
    let collapse = collapse(&block.strings, block.letters);
    assert_eq!(
        collapse.rules,
        BTreeSet::from([word(&[looped, unlooped]), word(&[unlooped, looped])])
    );
    let pairs = BTreeSet::from([
        (
            word(&[looped, unlooped, looped]),
            word(&[looped, unlooped]),
            word(&[unlooped, looped]),
        ),
        (
            word(&[unlooped, looped, unlooped]),
            word(&[unlooped, looped]),
            word(&[looped, unlooped]),
        ),
    ]);
    assert_eq!(
        collapse.pairs, pairs,
        "the essential cells of dimension three"
    );
    assert_eq!(block.certified, pairs, "the pairs completion certifies");
    let triples = BTreeSet::from([
        (
            word(&[looped, unlooped, looped, unlooped]),
            word(&[looped, unlooped]),
            word(&[unlooped, looped]),
            word(&[looped, unlooped]),
        ),
        (
            word(&[unlooped, looped, unlooped, looped]),
            word(&[unlooped, looped]),
            word(&[looped, unlooped]),
            word(&[unlooped, looped]),
        ),
    ]);
    assert_eq!(
        collapse.triples, triples,
        "the essential cells of dimension four"
    );
    assert_eq!(block.triples, triples, "the critical triples of the cells");
}

#[test]
fn every_unary_corpus_block_collapses_onto_its_rules_pairs_and_triples_but_one()
{
    // Each unary corpus block's essential cells of dimension three are the
    // pairs completion certifies, and those of dimension four are the critical
    // triples of its cells. Those of dimension two are its rules' left sides,
    // on every block but `IntOp`: its rule `pred x <=> P x` has a left side of
    // one letter, so `pred` is no normal form, and the collapse drops the
    // letter with the rule. A block with a triple longer than the truncation
    // is undecided in dimension four.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let mut blocks = 0_usize;
    let mut apart: Vec<String> = Vec::new();
    let mut undecided: Vec<String> = Vec::new();
    let mut lefts: BTreeSet<Word> = BTreeSet::new();
    for path in corpus() {
        let text = std::fs::read_to_string(&path).expect("a corpus source reads");
        let source = SourceText::from(text.as_str());
        let named = path.strip_prefix(&root).expect("a corpus path");
        let _lowering = each_block(&grammar, source, |cells| {
            let Some(block) = unary(cells)
            else {
                return;
            };
            if block.strings.rules.is_empty() {
                return;
            }
            blocks += 1;
            let collapse = collapse(&block.strings, block.letters);
            assert_eq!(
                collapse.pairs,
                block.certified,
                "{}: the essential pairs are the certified ones",
                named.display()
            );
            if block
                .triples
                .iter()
                .any(|&(ref peak, ..)| peak.0.len() > WORD_BUDGET)
            {
                undecided.push(named.display().to_string());
            }
            else {
                assert_eq!(
                    collapse.triples,
                    block.triples,
                    "{}: the essential cells of dimension four are the critical triples",
                    named.display()
                );
            }
            lefts.clear();
            lefts.extend(
                block
                    .strings
                    .rules
                    .iter()
                    .map(|&(ref left, _)| left.clone()),
            );
            if collapse.rules != lefts {
                assert!(
                    lefts
                        .difference(&collapse.rules)
                        .all(|left| left.0.len() == 1)
                        && collapse.rules.is_subset(&lefts),
                    "{}: only a rule with a one-letter left side drops: {lefts:?} against {:?}",
                    named.display(),
                    collapse.rules
                );
                apart.push(named.display().to_string());
            }
        });
    }
    assert!(blocks > 1, "the corpus holds unary blocks");
    assert_eq!(
        apart,
        ["model/data/arrows.gandr"],
        "the blocks whose rules a letter's definition shortens"
    );
    assert!(
        undecided.is_empty(),
        "every block decides dimension four within the truncation: {undecided:?}"
    );
}

/// One pair of a scheme's matching, read alone: the pair keeps its classes,
/// and every other cell is critical. The scheme's faces are read unchanged.
struct Alone<'scheme, S>
where
    S: Scheme,
{
    /// The scheme read.
    scheme: &'scheme mut S,
    /// The redundant cell of the pair.
    redundant: S::Cell,
    /// Its partner one dimension up.
    partner: S::Cell,
}

impl<S> Complex for Alone<'_, S>
where
    S: Scheme,
{
    type Cell = S::Cell;
    type Fault = S::Fault;

    /// The scheme's standing.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        cell: &S::Cell,
    ) -> Result<Standing, S::Fault>
    {
        self.scheme.standing(cell)
    }

    /// The scheme's faces.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &S::Cell,
        faces: &mut Vec<(S::Cell, Incidence)>,
    ) -> Result<(), S::Fault>
    {
        self.scheme.faces(cell, faces)
    }

    /// The scheme's pairing condition.
    ///
    /// # Specification
    /// trivial.
    fn pairing(
        &mut self,
        face: &S::Cell,
        cell: &S::Cell,
        incidence: Incidence,
    ) -> Result<Invertibility, S::Fault>
    {
        self.scheme.pairing(face, cell, incidence)
    }
}

impl<S> Scheme for Alone<'_, S>
where
    S: Scheme,
{
    /// The pair's classes, and critical for every other cell.
    ///
    /// # Specification
    /// trivial.
    fn class(
        &mut self,
        cell: &S::Cell,
    ) -> Result<Class<S::Cell>, S::Fault>
    {
        Ok(if *cell == self.redundant {
            Class::Redundant(self.partner.clone())
        }
        else if *cell == self.partner {
            Class::Collapsible(self.redundant.clone())
        }
        else {
            Class::Critical
        })
    }
}

/// A cell of a unary block's written presentation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Written
{
    /// A letter, of dimension one.
    Letter(Letter),
    /// A rule by its place, of dimension two.
    Rule(usize),
}

/// A unary block's written presentation as integer chains, with one pair
/// matched. A rule's faces are the letters of its left side less those of its
/// right side.
struct Presented<'strings>
{
    /// The rules.
    strings: &'strings Strings,
    /// The number of letters.
    letters: LetterCount,
    /// The matched letter, then its rule.
    pair: (Written, Written),
}

impl Complex for Presented<'_>
{
    type Cell = Written;
    type Fault = Infallible;

    /// Inside for each letter and each rule of the block.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        cell: &Written,
    ) -> Result<Standing, Infallible>
    {
        let inside = match *cell {
            Written::Letter(Letter(at)) => at < self.letters.0,
            Written::Rule(at) => at < self.strings.rules.len(),
        };
        Ok(if inside {
            Standing::Inside
        }
        else {
            Standing::Outside
        })
    }

    /// A rule's letter counts, its left side less its right side; a letter
    /// has no faces.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &Written,
        faces: &mut Vec<(Written, Incidence)>,
    ) -> Result<(), Infallible>
    {
        faces.clear();
        let Written::Rule(at) = *cell
        else {
            return Ok(());
        };
        let Some(&(ref left, ref right)) = self.strings.rules.get(at)
        else {
            return Ok(());
        };
        let mut counts: BTreeMap<Letter, i64> = BTreeMap::new();
        for &letter in &left.0 {
            let count = counts.entry(letter).or_default();
            *count = count.saturating_add(1);
        }
        for &letter in &right.0 {
            let count = counts.entry(letter).or_default();
            *count = count.saturating_sub(1);
        }
        faces.extend(
            counts
                .into_iter()
                .filter(|&(_, count)| count != 0)
                .map(|(letter, count)| (Written::Letter(letter), Incidence::from(count))),
        );
        Ok(())
    }
}

impl Scheme for Presented<'_>
{
    /// The pair's classes, and critical for every other cell.
    ///
    /// # Specification
    /// trivial.
    fn class(
        &mut self,
        cell: &Written,
    ) -> Result<Class<Written>, Infallible>
    {
        let (letter, rule) = self.pair;
        Ok(if *cell == letter {
            Class::Redundant(rule)
        }
        else if *cell == rule {
            Class::Collapsible(letter)
        }
        else {
            Class::Critical
        })
    }
}

/// The `IntOp` block of the corpus, the one unary block whose rule defines a
/// letter, with that rule's place.
///
/// # Specification
/// trivial.
fn intop() -> (UnaryBlock, RuleIndex)
{
    let grammar = built_in().expect("the built-in grammar builds");
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/data/arrows.gandr");
    let text = std::fs::read_to_string(&path).expect("the arrows source reads");
    let mut blocks = Vec::new();
    let _lowering = each_block(&grammar, SourceText::from(text.as_str()), |cells| {
        let Some(block) = unary(cells)
        else {
            return;
        };
        let defining: Vec<usize> = block
            .strings
            .rules
            .iter()
            .enumerate()
            .filter(|&(_, &(ref left, _))| left.0.len() == 1)
            .map(|(at, _)| at)
            .collect();
        if let [rule] = *defining.as_slice() {
            blocks.push((block, RuleIndex(rule)));
        }
    });
    assert_eq!(blocks.len(), 1, "one block defines a letter");
    blocks.pop().expect("one block defines a letter")
}

#[test]
fn the_intop_letter_drops_by_one_tietze_move_before_brown_collapse_6059()
{
    // `IntOp`'s rule `pred x <=> P x` defines the letter `pred`. The bar
    // complex holds no cell of `pred`, which is no normal form, so Brown's
    // scheme removes no pair of it. The drop is one Tietze move on the
    // written presentation, the backward (T1) of § 5.1.1 of Ara and others.
    // The letter with its rule, matched alone on the presentation's chains,
    // is an equivalence that replays and defines the letter as `P`. Brown's
    // critical cells of dimensions one and two spell what the move leaves.
    let (block, RuleIndex(rule)) = intop();
    let (ref left, ref right) = *block.strings.rules.get(rule).expect("the rule is a rule");
    let [letter] = *left.0.as_slice()
    else {
        panic!("the rule's left side is one letter");
    };
    let [defined] = *right.0.as_slice()
    else {
        panic!("the rule's right side is one letter");
    };
    let mut written = Presented {
        strings: &block.strings,
        letters: block.letters,
        pair: (Written::Letter(letter), Written::Rule(rule)),
    };
    let presented: Vec<Written> = (0 .. block.letters.0)
        .map(|at| Written::Letter(Letter(at)))
        .chain((0 .. block.strings.rules.len()).map(Written::Rule))
        .collect();
    let room = Budget::from(presented.len());
    let mut chains = Abelian::new(&mut written);
    let one = equivalence(&mut chains, &presented, room).expect("one pair is acyclic");
    one.replay(&mut chains, &presented, room)
        .expect("the move replays");
    let [ref removal] = *one.removals()
    else {
        panic!("the move removes one pair");
    };
    let spelt = chains
        .generator(&Written::Letter(defined))
        .expect("the defining letter is a generator");
    assert_eq!(
        removal.definition().replacement,
        spelt,
        "the move defines the letter as its rule's right side"
    );
    let left_after: BTreeSet<(usize, Word)> = one
        .critical()
        .iter()
        .map(|&cell| match cell {
            Written::Letter(at) => (1, Word(vec![at])),
            Written::Rule(at) => {
                let (ref left, _) = *block.strings.rules.get(at).expect("the rule is a rule");
                (2, left.clone())
            },
        })
        .collect();
    let mut theory = theory(&block.strings, block.letters);
    let cells: Vec<BarCell> = bar_cells(&block.strings, block.letters)
        .iter()
        .flatten()
        .map(|words| bar_cell(theory.table_mut(), words))
        .collect();
    let dropped = bar_cell(theory.table_mut(), core::slice::from_ref(left));
    assert!(
        !cells.contains(&dropped),
        "the bar complex holds no cell of the letter"
    );
    let room = Budget::from(cells.len());
    let brown = equivalence(&mut Abelian::new(&mut theory), &cells, room)
        .expect("Brown's scheme is acyclic");
    let critical: BTreeSet<(usize, Word)> = brown
        .critical()
        .iter()
        .filter(|cell| matches!(cell.0.len(), 1 | 2))
        .map(|cell| {
            let words = entries(theory.table(), cell).expect("a bar cell spells words");
            (
                words.len(),
                Word(
                    words
                        .iter()
                        .flat_map(|word| word.0.iter().copied())
                        .collect(),
                ),
            )
        })
        .collect();
    assert_eq!(
        critical, left_after,
        "Brown's critical cells spell what the move leaves"
    );
}

#[test]
fn brown_collapse_of_intop_factors_through_its_tietze_moves_6059()
{
    // Each removal of Brown's scheme on `IntOp`'s bar complex removes a cell
    // that its partner defines: one Tietze move of the resolution. Matched
    // alone, each removal is an equivalence that replays, and the scheme
    // collapses each cell as its moves do, the last removal first.
    let (block, _) = intop();
    let mut theory = theory(&block.strings, block.letters);
    let cells: Vec<BarCell> = bar_cells(&block.strings, block.letters)
        .iter()
        .flatten()
        .map(|words| bar_cell(theory.table_mut(), words))
        .collect();
    let room = Budget::from(cells.len());
    let mut chains = Abelian::new(&mut theory);
    let scheme = equivalence(&mut chains, &cells, room).expect("Brown's scheme is acyclic");
    let mut bound = scheme
        .on(&mut chains, &cells, room)
        .expect("the scheme reads on its chains");
    assert_eq!(bound.replay(), Ok(()), "the scheme replays as a reduction");
    let mut reduced = Vec::with_capacity(cells.len());
    for cell in &cells {
        let own = bound.generator(cell).expect("the cell is a generator");
        reduced.push(bound.collapse(&own).expect("the scheme collapses it"));
    }
    let mut moved: Vec<Chain<BarCell>> = Vec::with_capacity(cells.len());
    for cell in &cells {
        moved.push(chains.generator(cell).expect("the cell is a generator"));
    }
    for removal in scheme.removals().iter().rev() {
        let mut alone = Alone {
            scheme: &mut theory,
            redundant: removal.redundant().clone(),
            partner: removal.partner().clone(),
        };
        let mut chains = Abelian::new(&mut alone);
        let one = equivalence(&mut chains, &cells, room).expect("one pair is acyclic");
        assert_eq!(one.removals().len(), 1, "the move removes one pair");
        let mut each = one
            .on(&mut chains, &cells, room)
            .expect("the move reads on its chains");
        assert_eq!(each.replay(), Ok(()), "the move replays as a reduction");
        for image in &mut moved {
            *image = each.collapse(image).expect("the move collapses it");
        }
    }
    assert_eq!(
        moved, reduced,
        "the moves collapse each cell as the scheme does"
    );
}

/// Whether each rule keeps its variables: each occurs as often on its right
/// side as on its left.
///
/// # Specification
/// trivial.
fn balanced(rules: &[(FreeTerm, FreeTerm)]) -> Reducibility
{
    let occurrences = |term: &FreeTerm| {
        let mut counts: BTreeMap<String, Coefficient> = BTreeMap::new();
        let mut pending: Vec<TermView<'_>> = vec![term.view()];
        while let Some(view) = pending.pop() {
            match view {
                TermView::Var(name) => {
                    let count = counts.entry(String::from(name.as_ref())).or_default();
                    count.0 = count.0.saturating_add(1);
                },
                TermView::Ctor { args, .. }
                | TermView::Op { args, .. }
                | TermView::Results { args }
                | TermView::Inst { args, .. }
                | TermView::Abs { args, .. }
                | TermView::Lam { args, .. } => pending.extend(args.map(TermNode::view)),
                TermView::Atom(_) | TermView::Bound(_) => {},
            }
        }
        counts
    };
    if rules
        .iter()
        .all(|&(ref left, ref right)| occurrences(left) == occurrences(right))
    {
        Reducibility::Irreducible
    }
    else {
        Reducibility::Reducible
    }
}

#[test]
fn squier_homology_closes_on_every_corpus_block_whose_rules_keep_their_variables()
{
    // A rule that erases or copies a variable changes the symbols of what the
    // variable stands for, which the abelianised boundary does not see. On
    // every other block the two joining paths of each pair change the symbols
    // alike, so the small complex is a complex.
    let grammar = built_in().expect("the built-in grammar builds");
    let mut closed = 0_usize;
    for path in corpus() {
        let text = std::fs::read_to_string(&path).expect("a corpus source reads");
        let source = SourceText::from(text.as_str());
        let named = path.display();
        let _lowering = each_block(&grammar, source, |cells| {
            for (reading, complex) in small_complexes(cells) {
                let Some(complex) = complex
                else {
                    continue;
                };
                if complex.closed() == Reducibility::Irreducible {
                    closed += 1;
                    assert!(complex.homology().is_some(), "{named} {reading:?}");
                }
                else {
                    let rules = rules_of(cells, reading);
                    assert_eq!(
                        balanced(&rules),
                        Reducibility::Reducible,
                        "{named} {reading:?}: a block whose rules keep their variables closes"
                    );
                }
            }
        });
    }
    assert!(
        closed > 1,
        "the corpus holds blocks whose small complex closes"
    );
}

/// The rules of one reading of `cells`, as `small_complexes` reads them.
///
/// # Specification
/// trivial.
pub fn rules_of(
    cells: &DeclarationCells,
    reading: Reading,
) -> Vec<(FreeTerm, FreeTerm)>
{
    match reading {
        Reading::Terms => match cells.presented {
            Maybe::Present(ref presented) => presented
                .store
                .iter()
                .filter_map(|(_, cell)| Some((spelled(cell.lhs())?, spelled(cell.rhs())?)))
                .collect(),
            Maybe::Absent(_) => Vec::new(),
        },
        Reading::Commands => cells
            .oriented
            .iter()
            .map(|rule| (rule.lhs.clone(), rule.rhs.clone()))
            .collect(),
    }
}

#[test]
fn the_blocks_of_5258_have_the_homology_their_pairs_give()
{
    // `NatUnits` joins in the sequent reading. Its rules' boundaries span one
    // line, `add` and `Zero` together, so two of its three symbols stay. Its
    // two pairs' boundaries, `ρ1 − ρ2` and `−ρ3`, fill the rules' cycles.
    // `NatAssoc` reads its associativity over terms. `NatApart` is refused,
    // so it has no complex.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let mut found: Vec<(String, Reading, Option<Homology>)> = Vec::new();
    for (file, block) in [
        ("model/desc/rules-overlap-joinable.gandr", "data NatUnits"),
        (
            "ledger/features/nested-operation-laws.gandr",
            "data NatAssoc",
        ),
        ("pathological/desc/rules-diverge.gandr", "data NatApart"),
    ] {
        let text = std::fs::read_to_string(root.join(file)).expect("a corpus source reads");
        let source = SourceText::from(text.as_str());
        let _lowering = each_block(&grammar, source, |cells| {
            let named = source
                .fragment(cells.at.span)
                .map(|fragment| fragment.as_ref().starts_with(block));
            if !matches!(named, Ok(true)) {
                return;
            }
            if certified(cells).is_none() {
                found.push((String::from(block), Reading::Terms, None));
            }
            for (reading, complex) in small_complexes(cells) {
                found.push((
                    String::from(block),
                    reading,
                    complex.and_then(|complex| complex.homology()),
                ));
            }
        });
    }
    let homology = |first: usize, second: usize, third: usize| {
        Some(Homology {
            first: Rank(first),
            second: Rank(second),
            third_at_most: Rank(third),
        })
    };
    assert_eq!(found, [
        (
            String::from("data NatUnits"),
            Reading::Commands,
            homology(2, 0, 0)
        ),
        (
            String::from("data NatAssoc"),
            Reading::Terms,
            homology(2, 0, 1)
        ),
        (
            String::from("data NatAssoc"),
            Reading::Commands,
            homology(2, 1, 0)
        ),
        (String::from("data NatApart"), Reading::Terms, None),
    ]);
}
