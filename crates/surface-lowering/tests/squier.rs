//! Probe 1 of the presented-spaces frame, run where the frame places it.
//!
//! The frame reads completion's critical pairs as the critical cells of a
//! collapse of the standard resolution. For a block whose operations are all
//! unary, the rules are a string rewriting system, and the block presents a
//! monoid. The standard resolution of a monoid is its bar complex. Its cells
//! are the tuples of nonempty normal forms. Brown's collapsing scheme, along
//! the rules, pairs every other cell and leaves Anick's chains: the letters,
//! the rules' left sides, and the chains of overlaps of two left sides. The
//! suite builds the bar complex of each such block of the corpus, truncated
//! at a word length, collapses it, and compares the chains of dimensions two
//! and three with the rules and the pairs that completion certifies.
//!
//! The suite also computes Squier's homology over the rationals on the small
//! complex of every block of the corpus: one cell for each symbol, each rule
//! and each certified pair. A rule's boundary counts the symbols of its left
//! side less those of its right side. A pair's boundary counts the rules along
//! its first joining path less those along its second.
//!
//! A block with a binary operation presents a Lawvere theory, whose bar
//! complex no crate builds. The suite counts such a block as undecided for
//! the collapse and never as a pass.

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
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_computads::EtaElaboration;
use gandr_theory_computads::Term;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Scheme;
use gandr_theory_discrete_morse::Standing;
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

    /// The normal form of `word`, the leftmost redex first at each step.
    ///
    /// # Specification
    /// trivial.
    fn normal(
        &self,
        word: &Word,
    ) -> Word
    {
        let mut current = word.0.clone();
        for _ in 0_u32 .. 1_000_u32 {
            let redex = (0 .. current.len()).find_map(|start| {
                self.rules.iter().find_map(|&(ref left, ref right)| {
                    current
                        .get(start .. start.saturating_add(left.0.len()))
                        .filter(|window| *window == left.0.as_slice() && !left.0.is_empty())
                        .map(|_| (start, left.0.len(), right))
                })
            });
            let Some((start, width, right)) = redex
            else {
                return Word(current);
            };
            let _removed: Vec<Letter> = current
                .splice(
                    start .. start.saturating_add(width),
                    right.0.iter().copied(),
                )
                .collect();
        }
        panic!("a terminating block normalizes {word:?} within a thousand steps")
    }
}

/// A cell of the bar complex: a tuple of nonempty normal forms.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BarCell(Vec<Word>);

/// A coefficient of a boundary.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Coefficient(i64);

/// The class of `cell` under the collapsing scheme of `strings`.
///
/// The first entry must be a letter, else the cell is redundant and pairs with
/// the cell that splits its first letter off. Then, for each entry after the
/// first, the previous entry and this one must join to a reducible word whose
/// first redex ends at the end of this entry. A pair that joins to a normal
/// form makes the cell collapsible onto the cell that joins them. A redex that
/// ends inside the entry makes the cell redundant, paired with the cell that
/// splits the entry after the redex.
///
/// # Specification
/// trivial.
fn class(
    strings: &Strings,
    cell: &BarCell,
) -> Class<BarCell>
{
    let entries = &cell.0;
    let Some(first) = entries.first()
    else {
        return Class::Critical;
    };
    if first.0.len() >= 2 {
        let mut split = Vec::with_capacity(entries.len().saturating_add(1));
        split.push(Word(first.0[.. 1].to_vec()));
        split.push(Word(first.0[1 ..].to_vec()));
        split.extend(entries.iter().skip(1).cloned());
        return Class::Redundant(BarCell(split));
    }
    for index in 1 .. entries.len() {
        let (before, after) = (index.saturating_sub(1), index.saturating_add(1));
        let (previous, current) = (&entries[before], &entries[index]);
        let joined = previous.then(current);
        if strings.reducibility(&joined) == Reducibility::Irreducible {
            let mut merged: Vec<Word> = entries[.. before].to_vec();
            merged.push(joined);
            merged.extend(entries[after ..].iter().cloned());
            return Class::Collapsible(BarCell(merged));
        }
        let shortest = (1 ..= current.0.len())
            .find(|&length| {
                strings.reducibility(&previous.then(&Word(current.0[.. length].to_vec())))
                    == Reducibility::Reducible
            })
            .expect("the joined word is reducible");
        if shortest < current.0.len() {
            let mut split: Vec<Word> = entries[.. index].to_vec();
            split.push(Word(current.0[.. shortest].to_vec()));
            split.push(Word(current.0[shortest ..].to_vec()));
            split.extend(entries[after ..].iter().cloned());
            return Class::Redundant(BarCell(split));
        }
    }
    Class::Critical
}

/// The boundary of `cell` in the bar complex with trivial coefficients: the
/// cell without its first entry, each two neighbours joined with an
/// alternating sign, and the cell without its last entry. A join to the empty
/// word is degenerate and dropped.
///
/// # Specification
/// trivial.
fn boundary(
    strings: &Strings,
    cell: &BarCell,
) -> BTreeMap<BarCell, Coefficient>
{
    let entries = &cell.0;
    let count = entries.len();
    let mut out: BTreeMap<BarCell, Coefficient> = BTreeMap::new();
    let mut add = |face: Vec<Word>, sign: i64| {
        let entry = out.entry(BarCell(face)).or_default();
        entry.0 = entry.0.saturating_add(sign);
    };
    if count == 0 {
        return out;
    }
    add(entries[1 ..].to_vec(), 1);
    for index in 1 .. count {
        let (before, after) = (index.saturating_sub(1), index.saturating_add(1));
        let joined = strings.normal(&entries[before].then(&entries[index]));
        if joined.0.is_empty() {
            continue;
        }
        let mut face: Vec<Word> = entries[.. before].to_vec();
        face.push(joined);
        face.extend(entries[after ..].iter().cloned());
        add(face, if index % 2 == 1 { -1 } else { 1 });
    }
    add(
        entries[.. count.saturating_sub(1)].to_vec(),
        if count % 2 == 1 { -1 } else { 1 },
    );
    out.retain(|_, coefficient| coefficient.0 != 0);
    out
}

/// A unary block's bar complex under Brown's collapsing scheme, as the Morse
/// crate reads it.
#[repr(transparent)]
struct Bar<'strings>
{
    /// The block's rules as a string rewriting system.
    strings: &'strings Strings,
}

impl Complex for Bar<'_>
{
    type Cell = BarCell;
    type Fault = Infallible;

    /// Whether each entry of `cell` is a nonempty normal form.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        cell: &BarCell,
    ) -> Result<Standing, Infallible>
    {
        let normal = cell.0.iter().all(|word| {
            !word.0.is_empty() && self.strings.reducibility(word) == Reducibility::Irreducible
        });
        Ok(if normal {
            Standing::Inside
        }
        else {
            Standing::Outside
        })
    }

    /// The faces of `cell` in its boundary, each with its coefficient.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &BarCell,
        faces: &mut Vec<(BarCell, Incidence)>,
    ) -> Result<(), Infallible>
    {
        faces.extend(
            boundary(self.strings, cell)
                .into_iter()
                .map(|(face, coefficient)| (face, Incidence::from(coefficient.0))),
        );
        Ok(())
    }
}

impl Scheme for Bar<'_>
{
    /// The class of `cell` under Brown's collapsing scheme.
    ///
    /// # Specification
    /// trivial.
    fn class(
        &mut self,
        cell: &BarCell,
    ) -> Result<Class<BarCell>, Infallible>
    {
        Ok(class(self.strings, cell))
    }
}

/// Every cell of the bar complex of `strings` over `letters` letters, its
/// entries' lengths summing to at most [`WORD_BUDGET`], by dimension.
///
/// # Specification
/// trivial.
fn bar_cells(
    strings: &Strings,
    letters: LetterCount,
) -> Vec<Vec<BarCell>>
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
    let mut by_dimension: Vec<Vec<BarCell>> = vec![vec![BarCell(Vec::new())]];
    loop {
        let last = by_dimension.last().expect("the empty cell");
        let mut next = Vec::new();
        for cell in last {
            let used: usize = cell.0.iter().map(|word| word.0.len()).sum();
            for word in &normal {
                if used.saturating_add(word.0.len()) <= WORD_BUDGET {
                    let mut grown = cell.0.clone();
                    grown.push(word.clone());
                    next.push(BarCell(grown));
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
/// of dimension two as words, and those of dimension three as their peak, the
/// left side at its start and the left side at its end.
#[derive(Debug, Default, Eq, PartialEq)]
struct Collapse
{
    /// The words of the essential cells of dimension two.
    rules: BTreeSet<Word>,
    /// The peak and the two left sides of each essential cell of dimension
    /// three.
    pairs: BTreeSet<(Word, Word, Word)>,
    /// The number of cells of each dimension.
    cells: Vec<Rank>,
}

/// Collapse the bar complex of `strings`. The Morse crate checks that the
/// scheme is an acyclic matching: each pair's partner names it back, the
/// redundant cell has the coefficient one or minus one in its partner's
/// boundary, and the gradient has no cycle.
///
/// # Specification
/// trivial.
fn collapse(
    strings: &Strings,
    letters: LetterCount,
) -> Collapse
{
    let by_dimension = bar_cells(strings, letters);
    let mut twice: BTreeMap<BarCell, Coefficient> = BTreeMap::new();
    for cell in by_dimension.iter().flatten() {
        twice.clear();
        for (face, outer) in boundary(strings, cell) {
            for (deeper, inner) in boundary(strings, &face) {
                let entry = twice.entry(deeper).or_default();
                entry.0 = entry.0.saturating_add(outer.0.saturating_mul(inner.0));
            }
        }
        assert!(
            twice.values().all(|coefficient| coefficient.0 == 0),
            "the boundary of the boundary of {cell:?} is zero"
        );
    }
    // A partner keeps the letters of its cell, so the walk stays inside the
    // truncation and visits fewer cells than it holds.
    let held = by_dimension
        .iter()
        .map(Vec::len)
        .fold(0_usize, usize::saturating_add);
    let done = gandr_theory_discrete_morse::collapse(
        &mut Bar { strings },
        by_dimension.iter().flatten(),
        Budget::from(held),
    )
    .expect("the walk stays inside the truncation");
    assert_eq!(
        done.faults(),
        Faults::default(),
        "Brown's scheme is an acyclic matching"
    );
    let mut out = Collapse {
        cells: by_dimension.iter().map(|cells| Rank(cells.len())).collect(),
        ..Collapse::default()
    };
    for cell in done.critical() {
        match *cell.0.as_slice() {
            [ref x, ref u] => {
                let _new = out.rules.insert(x.then(u));
            },
            [ref x, ref u, ref v] => {
                let peak = x.then(u).then(v);
                let tail = u.then(v);
                let end = strings
                    .rules
                    .iter()
                    .map(|&(ref left, _)| left)
                    .filter(|left| tail.0.ends_with(&left.0))
                    .max_by_key(|left| left.0.len())
                    .expect("a chain ends with a left side")
                    .clone();
                let _new = out.pairs.insert((peak, x.then(u), end));
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

/// A unary block read as strings: its rules, its letter count, and the
/// certified pairs of its presented reading as their peak and two left sides.
struct UnaryBlock
{
    /// The rules as a string rewriting system.
    strings: Strings,
    /// The number of letters.
    letters: LetterCount,
    /// The certified pairs.
    certified: BTreeSet<(Word, Word, Word)>,
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
    Some(UnaryBlock {
        strings: Strings { rules },
        letters: LetterCount(u8::try_from(names.len()).expect("a small alphabet")),
        certified: pairs,
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
fn the_circles_bar_complex_collapses_onto_its_two_rules_and_two_certified_pairs()
{
    // The letters are `Loop` and `Unloop`, in name order. Brown's scheme keeps
    // `[Loop|Unloop]` and `[Unloop|Loop]`, the two left sides, and
    // `[Loop|Unloop|Loop]` and `[Unloop|Loop|Unloop]`, the two overlaps.
    // Completion certifies the same two overlaps.
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
}

#[test]
fn every_unary_corpus_block_collapses_onto_its_rules_and_certified_pairs_but_one()
{
    // Each unary corpus block's essential cells of dimension three are the
    // pairs completion certifies. Those of dimension two are its rules' left
    // sides, on every block but `IntOp`: its rule `pred x <=> P x` has a left
    // side of one letter, so `pred` is no normal form, and the collapse drops
    // the letter with the rule.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let mut blocks = 0_usize;
    let mut apart: Vec<String> = Vec::new();
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
