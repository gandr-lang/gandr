//! Probe 1 of the presented-spaces frame, part B, first slice: the bar complex
//! of the Lawvere theory that a binary rule block presents.
//!
//! A first-order rule block presents a Lawvere theory. A morphism from `m` to
//! `k` is a tuple of `k` terms in `m` variables. Composition substitutes. A
//! convergent block gives each morphism one tuple of normal forms. The
//! ordinary homology of this category is trivial, because the object zero is
//! terminal. So Malbos and Mimram take the coefficients in a ringoid of
//! bicontexts. With trivial coefficients, an operation of arity `a` has the
//! boundary `a − 1`. A rule has the symbols of its right side less those of its
//! left side.
//!
//! The suite builds the bar complex of that homology. A cell of degree `n` is a
//! composable list `[u₁|u₂|…|uₙ]` of tuples of normal forms in context. The
//! tuple `u₁` holds one term. Each later tuple fills the variables of the
//! tuple before it. A cell is degenerate when `u₁` is a variable or a later
//! tuple is an identity. A degenerate cell is zero.
//!
//! | Face | Chain |
//! | --- | --- |
//! | first | `Σⱼ occⱼ(u₁) [u₂ⱼ|u₃|…|uₙ]`, a term for each variable of `u₁`, counted by its occurrences |
//! | inner, at `i` from 1 to `n − 1` | `(−1)ⁱ [u₁|…|uᵢ ∘ uᵢ₊₁|…|uₙ]`, the composite in normal form |
//! | last | `(−1)ⁿ [u₁|…|uₙ₋₁]` |
//!
//! A cell of degree one has the boundary `(occ(u₁) − 1) []`. The first face
//! counts occurrences. So the boundary of a boundary is zero only when each
//! rule keeps the occurrences of its variables.
//!
//! The complex is infinite. The suite bounds the variables of each tuple and
//! the total size of a cell's terms. It takes the largest subcomplex inside the
//! bound. The homology in each degree is the image of the cycles under a small
//! bound in the homology under a large bound. The suite takes each rank modulo
//! two large primes, and the two ranks must agree.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use std::path::Path;

use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use gandr_theory_coherent_resolutions::Arity;
use gandr_theory_coherent_resolutions::Arrow;
use gandr_theory_coherent_resolutions::BarBound;
use gandr_theory_coherent_resolutions::BarCell;
use gandr_theory_coherent_resolutions::BarDegree;
use gandr_theory_coherent_resolutions::LawvereTheory;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermSize;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Truncation;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_discrete_morse::Complex as _;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use crate::squier::Reading;
use crate::squier::certified;
use crate::squier::each_block;
use crate::squier::rules_of;
use crate::squier::small_complexes;

/// A count: of variables, of arguments, of the nodes of a term, of cells.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Count(pub usize);

/// A coefficient of a chain.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Coefficient(pub i64);

/// A chain of the bar complex: cells with nonzero coefficients.
pub type Chain = BTreeMap<BarCell, Coefficient>;

/// The most rewrites one normal form takes before the probe gives up.
pub const FUEL: usize = 100_000;

/// The highest degree the probe builds: three, so the homology of degree two
/// has its boundaries.
const TOP: usize = 3;

/// The boundary of `cell` as a chain, or none when a composite has no normal
/// form within the fuel.
///
/// # Specification
/// trivial.
pub fn boundary(
    theory: &mut LawvereTheory,
    cell: &BarCell,
) -> Option<Chain>
{
    let mut faces = Vec::new();
    theory.faces(cell, &mut faces).ok()?;
    Some(
        faces
            .into_iter()
            .map(|(face, incidence)| (face, Coefficient(i64::from(incidence))))
            .collect(),
    )
}

/// The faces that `truncation` lists for `cell`, as a chain, or none when the
/// truncation does not hold the cell.
///
/// # Specification
/// trivial.
fn listed(
    truncation: &Truncation,
    cell: &BarCell,
) -> Option<Chain>
{
    match truncation.faces(cell) {
        Maybe::Present(faces) => Some(
            faces
                .iter()
                .map(|&(ref face, incidence)| (face.clone(), Coefficient(i64::from(incidence))))
                .collect(),
        ),
        Maybe::Absent(_) => None,
    }
}

/// The bound of `variables` variables in each context and a total size of
/// `weight`, up to the probe's top degree.
///
/// # Specification
/// trivial.
pub fn bound(
    variables: Count,
    weight: Count,
) -> BarBound
{
    BarBound {
        variables: Arity::from(variables.0),
        weight: TermSize::from(weight.0),
        degree: BarDegree::from(TOP),
    }
}

/// The theory of `arities` and `rules` over `table`, under the probe's fuel.
///
/// # Specification
/// trivial.
pub fn theory(
    arities: Vec<Arity>,
    rules: Vec<(TermPlace, TermPlace)>,
    table: TermTable,
) -> LawvereTheory
{
    LawvereTheory::new(arities, rules, table, NormalizationBudget::from(FUEL))
}

/// A residue modulo a prime.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Residue(u64);

/// A prime modulus.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Prime(u64);

/// The two primes the ranks are taken modulo.
const PRIMES: [Prime; 2] = [Prime((1 << 61) - 1), Prime((1 << 31) - 1)];

impl Prime
{
    /// The residue of `coefficient`.
    ///
    /// # Specification
    /// trivial.
    fn residue(
        self,
        coefficient: Coefficient,
    ) -> Residue
    {
        let modulus = i128::from(self.0);
        Residue(u64::try_from(i128::from(coefficient.0).rem_euclid(modulus)).unwrap_or_default())
    }

    /// The product of two residues.
    ///
    /// # Specification
    /// trivial.
    fn times(
        self,
        left: Residue,
        right: Residue,
    ) -> Residue
    {
        let product = u128::from(left.0)
            .wrapping_mul(u128::from(right.0))
            .checked_rem(u128::from(self.0))
            .unwrap_or_default();
        Residue(u64::try_from(product).unwrap_or_default())
    }

    /// The difference of two residues.
    ///
    /// # Specification
    /// trivial.
    fn minus(
        self,
        left: Residue,
        right: Residue,
    ) -> Residue
    {
        // Both residues lie below the prime, so the sum stays positive.
        let difference = u128::from(left.0)
            .wrapping_add(u128::from(self.0))
            .wrapping_sub(u128::from(right.0))
            .checked_rem(u128::from(self.0))
            .unwrap_or_default();
        Residue(u64::try_from(difference).unwrap_or_default())
    }

    /// The inverse of a nonzero residue.
    ///
    /// # Specification
    /// trivial.
    fn inverse(
        self,
        value: Residue,
    ) -> Residue
    {
        let mut result = Residue(1);
        let mut base = value;
        let mut exponent = self.0.saturating_sub(2);
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = self.times(result, base);
            }
            base = self.times(base, base);
            exponent = exponent.checked_shr(1).unwrap_or_default();
        }
        result
    }
}

/// A sparse vector modulo a prime: each nonzero entry by its row.
type Sparse = BTreeMap<Count, Residue>;

/// Subtract `factor` times `pivot` from `vector`.
///
/// # Specification
/// trivial.
fn eliminate(
    prime: Prime,
    vector: &mut Sparse,
    (factor, pivot): (Residue, &Sparse),
)
{
    for (&row, &entry) in pivot {
        let next = prime.minus(
            vector.get(&row).copied().unwrap_or_default(),
            prime.times(factor, entry),
        );
        if next.0 == 0 {
            let _gone = vector.remove(&row);
        }
        else {
            let _previous = vector.insert(row, next);
        }
    }
}

/// Echelon vectors, each by its leading row, with the combination of inputs
/// that gives it.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Echelon
{
    /// The reduced vectors and their combinations, by leading row.
    pivots: BTreeMap<Count, (Sparse, Sparse)>,
}

impl Echelon
{
    /// Reduce `vector` by the pivots, and keep it when it does not vanish.
    /// Returns the combination of inputs that vanishes, or none.
    ///
    /// # Specification
    /// trivial.
    fn insert(
        &mut self,
        prime: Prime,
        mut vector: Sparse,
        mut tag: Sparse,
    ) -> Option<Sparse>
    {
        while let Some((&lead, &value)) = vector.iter().next() {
            let Some(&(ref pivot, ref pivot_tag)) = self.pivots.get(&lead)
            else {
                let _previous = self.pivots.insert(lead, (vector, tag));
                return None;
            };
            let leading = pivot.get(&lead).copied().unwrap_or(Residue(1));
            let factor = prime.times(value, prime.inverse(leading));
            eliminate(prime, &mut vector, (factor, pivot));
            eliminate(prime, &mut tag, (factor, pivot_tag));
        }
        Some(tag)
    }

    /// The rank of the vectors inserted.
    ///
    /// # Specification
    /// trivial.
    fn rank(&self) -> Count
    {
        Count(self.pivots.len())
    }

    /// Forget every vector.
    ///
    /// # Specification
    /// trivial.
    fn clear(&mut self)
    {
        self.pivots.clear();
    }
}

/// The dimension of the homology of each degree from zero to two: the image
/// of the cycles inside `small` in the homology inside `large`. Taken modulo
/// `prime`, or none when a cell or a face has no place.
///
/// # Specification
/// trivial.
fn persistent(
    (large, table): (&Truncation, &TermTable),
    small: BarBound,
    prime: Prime,
) -> Option<[Count; TOP]>
{
    let degrees: Vec<&[BarCell]> = (0 ..= TOP)
        .map(|degree| large.cells(BarDegree::from(degree)))
        .collect();
    let index: Vec<BTreeMap<&BarCell, Count>> = degrees
        .iter()
        .map(|cells| {
            cells
                .iter()
                .enumerate()
                .map(|(place, cell)| (cell, Count(place)))
                .collect()
        })
        .collect();
    let vector = |degree: usize, chain: &Chain| -> Option<Sparse> {
        let rows = index.get(degree)?;
        let mut out = Sparse::new();
        for (face, coefficient) in chain {
            let residue = prime.residue(*coefficient);
            if residue.0 != 0 {
                let _previous = out.insert(*rows.get(face)?, residue);
            }
        }
        Some(out)
    };
    let mut out = [Count(0); TOP];
    let (mut kernel, mut spanned) = (Echelon::default(), Echelon::default());
    let mut cycles: Vec<Sparse> = Vec::new();
    for (degree, slot) in out.iter_mut().enumerate() {
        let cells = *degrees.get(degree)?;
        let rows = index.get(degree)?;
        // The cycles among the cells inside the small bound.
        kernel.clear();
        cycles.clear();
        for cell in cells.iter().filter(|cell| {
            cell.weight(table)
                .is_ok_and(|weight| weight <= small.weight)
        }) {
            let place = *rows.get(cell)?;
            let image = if degree == 0 {
                Sparse::new()
            }
            else {
                vector(degree.saturating_sub(1), &listed(large, cell)?)?
            };
            if let Some(cycle) = kernel.insert(prime, image, Sparse::from([(place, Residue(1))])) {
                cycles.push(cycle);
            }
        }
        // The boundaries from the large bound, then the cycles beside them.
        spanned.clear();
        for cell in *degrees.get(degree.saturating_add(1))? {
            let image = vector(degree, &listed(large, cell)?)?;
            let _vanishing = spanned.insert(prime, image, Sparse::new());
        }
        let boundaries = spanned.rank();
        while let Some(cycle) = cycles.pop() {
            let _vanishing = spanned.insert(prime, cycle, Sparse::new());
        }
        *slot = Count(spanned.rank().0.saturating_sub(boundaries.0));
    }
    Some(out)
}

/// The bar complex's homology of degrees zero to two, and its cell counts of
/// degrees zero to three, under the large bound.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Bar
{
    /// The dimension of the homology of each degree.
    homology: [Count; TOP],
    /// The cells of each degree inside the large bound.
    cells: [Count; TOP + 1],
}

/// The bar complex of `theory`, its homology the image of `small` in `large`,
/// agreed modulo both primes; none past the fuel.
///
/// # Specification
/// trivial.
fn bar(
    theory: &mut LawvereTheory,
    (small, large): (BarBound, BarBound),
) -> Option<Bar>
{
    let truncation = theory.truncation(large).ok()?;
    let [first, second] =
        PRIMES.map(|prime| persistent((&truncation, theory.table()), small, prime));
    let homology = first?;
    assert_eq!(Some(homology), second, "the ranks agree modulo both primes");
    let mut cells = [Count(0); TOP + 1];
    for (degree, slot) in cells.iter_mut().enumerate() {
        *slot = Count(truncation.cells(BarDegree::from(degree)).len());
    }
    Some(Bar { homology, cells })
}

/// The cells of degrees two and three inside `bound` whose boundary has a
/// nonzero boundary.
///
/// # Specification
/// trivial.
fn unclosed(
    theory: &mut LawvereTheory,
    bound: BarBound,
) -> Vec<BarCell>
{
    let truncation = theory.truncation(bound).expect("the truncation builds");
    let mut out = Vec::new();
    let mut total = Chain::new();
    for cell in (2 ..= TOP).flat_map(|degree| truncation.cells(BarDegree::from(degree))) {
        total.clear();
        for (face, coefficient) in &listed(&truncation, cell).expect("a kept cell's faces") {
            for (inner, inner_coefficient) in &boundary(theory, face).expect("a face's boundary") {
                let entry = total.entry(inner.clone()).or_default();
                entry.0 = entry
                    .0
                    .saturating_add(coefficient.0.saturating_mul(inner_coefficient.0));
            }
        }
        if total.values().any(|coefficient| coefficient.0 != 0) {
            out.push(cell.clone());
        }
    }
    out
}

/// One step of the walk that reads a free term into a table.
#[derive(Clone, Copy, Debug)]
enum Walk<'term>
{
    /// Read the node.
    Enter(TermNode<'term>),
    /// Build an operation from the last `arity` terms read.
    Leave(Operation, Count),
}

/// The theory a block's rules present: each operation by the order of its
/// name, its arity from its uses. None when a rule's term binds, or its right
/// side holds a variable its left side lacks.
///
/// # Specification
/// trivial.
pub fn presented(rules: &[(FreeTerm, FreeTerm)]) -> Option<(LawvereTheory, Vec<String>)>
{
    let mut arities: BTreeMap<String, Count> = BTreeMap::new();
    let mut pending: Vec<TermView<'_>> = Vec::new();
    for &(ref left, ref right) in rules {
        pending.extend([left.view(), right.view()]);
    }
    while let Some(view) = pending.pop() {
        match view {
            TermView::Var(_) => {},
            TermView::Ctor { name, args } | TermView::Op { name, args } => {
                let _previous = arities.insert(String::from(name.as_ref()), Count(args.len()));
                pending.extend(args.map(TermNode::view));
            },
            TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => return None,
        }
    }
    let names: Vec<String> = arities.keys().cloned().collect();
    let mut table = TermTable::default();
    let mut out = Vec::with_capacity(rules.len());
    let mut variables: BTreeMap<String, Variable> = BTreeMap::new();
    for &(ref left, ref right) in rules {
        variables.clear();
        let left = read(left, (&names, &mut table), (&mut variables, Side::Left))?;
        let right = read(right, (&names, &mut table), (&mut variables, Side::Right))?;
        out.push((left, right));
    }
    Some((
        theory(
            arities
                .into_values()
                .map(|count| Arity::from(count.0))
                .collect(),
            out,
            table,
        ),
        names,
    ))
}

/// The term `term` read into `table`, each operation by its place in `names`.
/// A variable new on the left side takes the next place in `variables`. None
/// when the term binds, names an operation that `names` lacks, or holds on the
/// right side a variable that `variables` lacks.
///
/// # Specification
/// trivial.
pub fn read(
    term: &FreeTerm,
    (names, table): (&[String], &mut TermTable),
    (variables, side): (&mut BTreeMap<String, Variable>, Side),
) -> Option<TermPlace>
{
    let mut walk: Vec<Walk<'_>> = Vec::new();
    let mut arguments: Vec<TermNode<'_>> = Vec::new();
    let mut built: Vec<TermPlace> = Vec::new();
    let mut view = Some(term.view());
    loop {
        let step = match view.take() {
            Some(view) => Some(view),
            None => match walk.pop() {
                None => break,
                Some(Walk::Enter(node)) => Some(node.view()),
                Some(Walk::Leave(operation, arity)) => {
                    let start = built.len().checked_sub(arity.0)?;
                    let children = built.split_off(start);
                    built.push(table.op(operation, children).ok()?);
                    None
                },
            },
        };
        let Some(step) = step
        else {
            continue;
        };
        match step {
            TermView::Var(name) => {
                let name = String::from(name.as_ref());
                let next = Variable::from(variables.len());
                let variable = match (variables.get(&name), side) {
                    (Some(&held), _) => held,
                    (None, Side::Left) => {
                        let _new = variables.insert(name, next);
                        next
                    },
                    (None, Side::Right) => return None,
                };
                built.push(table.var(variable));
            },
            TermView::Ctor { name, args } | TermView::Op { name, args } => {
                let place = names
                    .binary_search_by(|held| held.as_str().cmp(name.as_ref()))
                    .ok()?;
                let operation = Operation::from(place);
                walk.push(Walk::Leave(operation, Count(args.len())));
                arguments.clear();
                arguments.extend(args);
                while let Some(argument) = arguments.pop() {
                    walk.push(Walk::Enter(argument));
                }
            },
            TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => return None,
        }
    }
    built.pop()
}

/// The side of a rule a term stands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Side
{
    /// The left side, which names the variables.
    Left,
    /// The right side, which uses only the left side's variables.
    Right,
}

/// The occurrences of each symbol in the term at `place` of `table`, each
/// path from the root counted once; none when a place is not in the table.
///
/// # Specification
/// trivial.
fn symbols(
    table: &TermTable,
    place: TermPlace,
) -> Option<BTreeMap<TermHead, Count>>
{
    let mut counts: BTreeMap<TermHead, Count> = BTreeMap::new();
    let mut pending = vec![place];
    while let Some(next) = pending.pop() {
        let node = table.node(next).ok()?;
        let count = counts.entry(node.head).or_default();
        count.0 = count.0.saturating_add(1);
        pending.extend(&node.children);
    }
    Some(counts)
}

/// The homology of degrees zero and one that the small complex gives once
/// each operation has the boundary `arity − 1`: one point, the operations,
/// and each rule's operations on its right side less those on its left.
///
/// # Specification
/// trivial.
fn with_operation_boundaries(theory: &LawvereTheory) -> [Count; 2]
{
    let prime = PRIMES[0];
    let mut operations = Echelon::default();
    for &arity in theory.arities() {
        let difference = Coefficient(
            i64::try_from(usize::from(arity))
                .unwrap_or(i64::MAX)
                .saturating_sub(1),
        );
        let mut column = Sparse::new();
        if difference.0 != 0 {
            let _previous = column.insert(Count(0), prime.residue(difference));
        }
        let _vanishing = operations.insert(prime, column, Sparse::new());
    }
    let mut rules = Echelon::default();
    for &(left, right) in theory.rules() {
        let (left, right) = (
            symbols(theory.table(), left).expect("a rule's left side"),
            symbols(theory.table(), right).expect("a rule's right side"),
        );
        let mut column = Sparse::new();
        for place in 0 .. theory.arities().len() {
            let head = TermHead::Op(Operation::from(place));
            let count = |counts: &BTreeMap<TermHead, Count>| {
                i64::try_from(counts.get(&head).copied().unwrap_or_default().0).unwrap_or(i64::MAX)
            };
            let residue = prime.residue(Coefficient(count(&right).saturating_sub(count(&left))));
            if residue.0 != 0 {
                let _previous = column.insert(Count(place), residue);
            }
        }
        let _vanishing = rules.insert(prime, column, Sparse::new());
    }
    [
        Count(1_usize.saturating_sub(operations.rank().0)),
        Count(
            theory
                .arities()
                .len()
                .saturating_sub(operations.rank().0)
                .saturating_sub(rules.rank().0),
        ),
    ]
}

/// The bounds of the probe: two variables, cycles of total size four, and
/// boundaries of total size six.
///
/// # Specification
/// trivial.
fn bounds() -> (BarBound, BarBound)
{
    (bound(Count(2), Count(4)), bound(Count(2), Count(6)))
}

/// The bounds one size smaller, to show the homology is stable.
///
/// # Specification
/// trivial.
fn smaller() -> (BarBound, BarBound)
{
    (bound(Count(2), Count(3)), bound(Count(2), Count(5)))
}

/// The theory of `arities` with no rule.
///
/// # Specification
/// trivial.
fn free(arities: &[Count]) -> LawvereTheory
{
    theory(
        arities.iter().map(|count| Arity::from(count.0)).collect(),
        Vec::new(),
        TermTable::default(),
    )
}

/// The circle: `Loop` and `Unloop`, each the other's inverse.
///
/// # Specification
/// trivial.
fn circle() -> LawvereTheory
{
    let (looped, unlooped) = (Operation::from(0_usize), Operation::from(1_usize));
    let mut table = TermTable::default();
    let x = table.var(Variable::from(0_usize));
    let mut op = |operation: Operation, child: TermPlace| {
        table
            .op(operation, vec![child])
            .expect("the circle's terms")
    };
    let (unloop_x, loop_x) = (op(unlooped, x), op(looped, x));
    let rules = vec![(op(looped, unloop_x), x), (op(unlooped, loop_x), x)];
    theory(
        vec![Arity::from(1_usize), Arity::from(1_usize)],
        rules,
        table,
    )
}

/// What the probe finds for one block: its name, its bar complex, its small
/// complexes' homology by reading, and the small complex's homology once
/// each operation has its boundary.
type Finding = (
    String,
    Option<Bar>,
    Vec<(Reading, Option<[Count; 2]>)>,
    Option<[Count; 2]>,
);

#[test]
fn the_cells_of_nat_units_to_size_three_have_boundaries_on_the_point()
{
    // The try-first of the unit. `NatUnits` has `Succ`, `Zero` and `add`, in
    // name order. Its normal forms to size three in at most two variables are
    // its cells of degree one, less the variables. Each boundary is a
    // multiple of the one cell of degree zero: the occurrences of the
    // variables, less one.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let text = std::fs::read_to_string(root.join("model/desc/rules-overlap-joinable.gandr"))
        .expect("a corpus source reads");
    let mut theories = Vec::new();
    let _lowering = each_block(&grammar, SourceText::from(text.as_str()), |cells| {
        if certified(cells).is_some() {
            theories
                .push(presented(&rules_of(cells, Reading::Commands)).expect("a first-order block"));
        }
    });
    let [(ref mut theory, ref names), ..] = *theories.as_mut_slice()
    else {
        panic!("the block of `NatUnits`");
    };
    assert_eq!(names, &["Succ", "Zero", "add"]);
    let (succ, zero, add) = (
        Operation::from(0_usize),
        Operation::from(1_usize),
        Operation::from(2_usize),
    );
    let table = theory.table_mut();
    let (x, y) = (
        table.var(Variable::from(0_usize)),
        table.var(Variable::from(1_usize)),
    );
    let mut op = |operation: Operation, children: Vec<TermPlace>| {
        table.op(operation, children).expect("a term of the block")
    };
    let constant = op(zero, Vec::new());
    let terms = [
        (0, op(zero, Vec::new()), -1),
        (0, op(succ, vec![constant]), -1),
        (1, op(succ, vec![x]), 0),
        (2, op(add, vec![x, y]), 1),
        (2, op(add, vec![x, x]), 1),
        (2, op(add, vec![y, x]), 1),
    ];
    let truncation = theory
        .truncation(bound(Count(2), Count(3)))
        .expect("the cells build");
    let degree_one: BTreeSet<&BarCell> =
        truncation.cells(BarDegree::from(1_usize)).iter().collect();
    let point = BarCell(Vec::new());
    for &(source, term, expected) in &terms {
        let held = BarCell(vec![Arrow {
            source: Arity::from(source),
            terms: vec![term],
        }]);
        assert!(degree_one.contains(&held), "{held:?} is a cell");
        let chain = listed(&truncation, &held).expect("a held cell's faces");
        let found = chain.get(&point).copied().unwrap_or_default();
        assert_eq!(found, Coefficient(expected), "{held:?}");
    }
    // Contexts of zero, one and two variables hold 3, 6 and 11 such terms.
    assert_eq!(degree_one.len(), 20);
    assert!(degree_one.iter().all(|cell| {
        listed(&truncation, cell).is_some_and(|chain| chain.keys().all(|face| *face == point))
    }));
}

#[test]
fn free_theories_and_the_circle_have_their_known_homology()
{
    // A free unary operation presents the free monoid on one letter, and the
    // circle presents the integers: both have the homology `1, 1, 0`. A free
    // binary operation and a free constant each bound the point, `2 − 1 = 1`
    // and `0 − 1 = −1`, so their homology is `0, 0, 0`.
    let homology =
        |theory: &mut LawvereTheory| bar(theory, bounds()).expect("the complex builds").homology;
    let ones = [Count(1), Count(1), Count(0)];
    let none = [Count(0), Count(0), Count(0)];
    assert_eq!(homology(&mut free(&[Count(1)])), ones);
    assert_eq!(homology(&mut circle()), ones);
    assert_eq!(homology(&mut free(&[Count(2)])), none);
    assert_eq!(homology(&mut free(&[Count(0)])), none);
}

#[test]
fn the_boundary_of_a_boundary_is_zero_when_each_rule_keeps_its_variables()
{
    // A rule that erases a variable changes the occurrences that the first
    // face counts: `d(t, x) ⇒ t` of the parallel disjunction leaves cells whose
    // boundary has a boundary.
    let limit = bound(Count(2), Count(5));
    assert!(unclosed(&mut circle(), limit).is_empty());
    let (disjunction, truth) = (Operation::from(0_usize), Operation::from(1_usize));
    let mut table = TermTable::default();
    let x = table.var(Variable::from(0_usize));
    let mut op = |operation: Operation, children: Vec<TermPlace>| {
        table.op(operation, children).expect("a term of the theory")
    };
    let constant = op(truth, Vec::new());
    let rules = vec![
        (op(disjunction, vec![constant, x]), constant),
        (op(disjunction, vec![x, constant]), constant),
    ];
    let mut erasing = theory(
        vec![Arity::from(2_usize), Arity::from(0_usize)],
        rules,
        table,
    );
    assert!(!unclosed(&mut erasing, limit).is_empty());
}

#[test]
fn the_blocks_of_5258_have_a_bar_homology_that_the_small_complex_misses_in_degree_one()
{
    // The probe. `NatUnits` and `NatAssoc` keep their variables, so their bar
    // complexes close. Both give the homology `0, 1, 0` at two bounds. The
    // small complex of #5365 has no cell of degree zero. It gives two classes
    // in degree one, since it leaves each operation without a boundary. With
    // the boundary `arity − 1` on each operation, the small complex gives
    // `0, 1` too. `NatApart` is refused, so it has no complex.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let mut found: Vec<Finding> = Vec::new();
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
            let small: Vec<(Reading, Option<[Count; 2]>)> = small_complexes(cells)
                .into_iter()
                .map(|(reading, complex)| {
                    let homology = complex.and_then(|complex| complex.homology());
                    (
                        reading,
                        homology
                            .map(|homology| [Count(homology.first.0), Count(homology.second.0)]),
                    )
                })
                .collect();
            if certified(cells).is_none() {
                found.push((String::from(block), None, small, None));
                return;
            }
            let (mut theory, _names) =
                presented(&rules_of(cells, Reading::Commands)).expect("a first-order block");
            assert!(
                unclosed(&mut theory, smaller().1).is_empty(),
                "{block} closes"
            );
            let stable = bar(&mut theory, smaller()).expect("the smaller complex builds");
            let complex = bar(&mut theory, bounds()).expect("the complex builds");
            assert_eq!(
                stable.homology, complex.homology,
                "{block}: the homology is stable"
            );
            let corrected = with_operation_boundaries(&theory);
            found.push((String::from(block), Some(complex), small, Some(corrected)));
        });
    }
    let bar_of = |homology: [usize; 3], cells: [usize; 4]| {
        Some(Bar {
            homology: homology.map(Count),
            cells: cells.map(Count),
        })
    };
    let two = |values: [usize; 2]| Some(values.map(Count));
    assert_eq!(found, [
        (
            String::from("data NatUnits"),
            bar_of([0, 1, 0], [1, 188, 1394, 3651]),
            vec![(Reading::Commands, two([2, 0]))],
            two([0, 1]),
        ),
        (
            String::from("data NatAssoc"),
            bar_of([0, 1, 0], [1, 169, 1665, 4009]),
            vec![
                (Reading::Terms, two([2, 0])),
                (Reading::Commands, two([2, 1]))
            ],
            two([0, 1]),
        ),
        (String::from("data NatApart"), None, Vec::new(), None),
    ]);
}
