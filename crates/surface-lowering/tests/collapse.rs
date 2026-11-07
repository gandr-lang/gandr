//! Probe 1 of the presented-spaces frame, part B, second slice: Brown's
//! collapsing scheme on the bar complex of a binary rule block.
//!
//! `theory-coherent-resolutions` gives each cell of the bar complex of a
//! block's Lawvere theory its class under Brown's collapsing scheme. The probe
//! lists the essential cells of degrees one to three through that scheme, and
//! checks the matching through the Morse crate.
//!
//! An essential cell of degree one is a generator. One of degree two is a
//! rule's left side `[f(x₁, …, xₐ)|y]`. One of degree three is an overlap of
//! two rules. The probe compares these cells with the rules and with the pairs
//! that completion certifies. The issue counts the rules and the pairs as
//! dimensions one and two. The bar complex holds the operations in degree one,
//! so the rules lie in its degree two.
//!
//! # References
//!
//! - `Malbos-2021-completion_operads_essential_syzygies` — newest: the
//!   essential syzygies of a convergent presentation, which the certified pairs
//!   are in degree three.
//! - `Doré-2023-computing_spaces_type_theory` — newest: § 3.4, a collapse whose
//!   class is a function, with a walk from each redundant cell.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use std::path::Path;

use gandr_surface_grammar::built_in;
use gandr_surface_lowering::coincide::Certificates;
use gandr_surface_lowering::desc_cells::DeclarationCells;
use gandr_surface_syntax::SourceText;
use gandr_theory_coherent_resolutions::Arity;
use gandr_theory_coherent_resolutions::Arrow;
use gandr_theory_coherent_resolutions::BarBound;
use gandr_theory_coherent_resolutions::BarCell;
use gandr_theory_coherent_resolutions::BarDegree;
use gandr_theory_coherent_resolutions::LawvereError;
use gandr_theory_coherent_resolutions::LawvereTheory;
use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Truncation;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Scheme as _;
use quenchant_shape::shape::Maybe;

use crate::lawvere::Count;
use crate::lawvere::Side;
use crate::lawvere::Unpresented;
use crate::lawvere::bound;
use crate::lawvere::presented;
use crate::lawvere::read;
use crate::squier::Presentation;
use crate::squier::Reading;
use crate::squier::certified;
use crate::squier::corpus;
use crate::squier::each_block;
use crate::squier::readings;
use crate::squier::rules_of;
use crate::squier::spelled;

/// The most redundant cells the cycle check visits before the probe gives up.
const CLOSURE: usize = 100_000;

/// The faults of the matching on the cells of degrees one and up of
/// `truncation`, through the Morse crate's check. Its walk starts at each
/// redundant cell and follows each redundant face of its partner, inside the
/// bound or outside it. None past the fuel or past [`CLOSURE`] redundant
/// cells.
///
/// # Specification
/// trivial.
fn faults(
    theory: &mut LawvereTheory,
    truncation: &Truncation,
) -> Option<Faults>
{
    let done = gandr_theory_discrete_morse::collapse(
        theory,
        (1 ..= DEGREES).flat_map(|degree| truncation.cells(BarDegree::from(degree))),
        Budget::from(CLOSURE),
    )
    .ok()?;
    Some(done.faults())
}

/// The degrees the probe classifies: one to three, the rules' overlaps in the
/// last.
const DEGREES: usize = 3;

/// The ways to write `total` as `parts` counts, each zero or more, in order.
///
/// # Specification
/// trivial.
fn spread(
    total: Count,
    parts: Count,
) -> Vec<Vec<Count>>
{
    let mut out = Vec::new();
    let mut pending: Vec<(Vec<Count>, Count)> = vec![(Vec::new(), total)];
    while let Some((prefix, remaining)) = pending.pop() {
        if prefix.len() == parts.0 {
            if remaining.0 == 0 {
                out.push(prefix);
            }
            continue;
        }
        for part in 0 ..= remaining.0 {
            let mut next = prefix.clone();
            next.push(Count(part));
            pending.push((next, Count(remaining.0.saturating_sub(part))));
        }
    }
    out
}

/// The terms of `theory` with `size` operations, each variable the hole `x₁`,
/// from the shapes with fewer operations.
///
/// # Specification
/// trivial.
fn shapes_of(
    theory: &mut LawvereTheory,
    shapes: &[Vec<TermPlace>],
    size: Count,
) -> Option<Vec<TermPlace>>
{
    let mut found = Vec::new();
    let mut tuples: Vec<Vec<TermPlace>> = Vec::new();
    let mut longer: Vec<Vec<TermPlace>> = Vec::new();
    for place in 0 .. theory.arities().len() {
        let operation = Operation::from(place);
        let arity = theory.arities().get(place).copied().unwrap_or_default();
        for sizes in spread(Count(size.0.saturating_sub(1)), Count(usize::from(arity))) {
            tuples.clear();
            tuples.push(Vec::new());
            for part in sizes {
                longer.clear();
                let arguments = shapes.get(part.0).map_or(&[][..], Vec::as_slice);
                for tuple in &tuples {
                    for &argument in arguments {
                        let mut next = tuple.clone();
                        next.push(argument);
                        longer.push(next);
                    }
                }
                core::mem::swap(&mut tuples, &mut longer);
            }
            while let Some(arguments) = tuples.pop() {
                found.push(theory.table_mut().op(operation, arguments).ok()?);
            }
        }
    }
    Some(found)
}

/// One step of the walk that numbers the variables of a term.
#[derive(Clone, Copy, Debug)]
enum Walk
{
    /// Read the node at the term.
    Enter(TermPlace),
    /// Make the operation from the last terms built, as many as the count.
    Leave(Operation, Count),
}

/// `arrow` with each variable replaced by a fresh variable, numbered in
/// pre-order across its terms, from as many variables as it holds.
///
/// # Specification
/// trivial.
fn numbered(
    table: &mut TermTable,
    arrow: &Arrow,
) -> Option<Arrow>
{
    let mut fresh = 0_usize;
    let mut terms = Vec::with_capacity(arrow.terms.len());
    let mut pending: Vec<Walk> = Vec::new();
    let mut built: Vec<TermPlace> = Vec::new();
    for &root in &arrow.terms {
        pending.push(Walk::Enter(root));
        while let Some(step) = pending.pop() {
            match step {
                Walk::Enter(place) => {
                    let node = table.node(place).ok()?;
                    match node.head {
                        TermHead::Op(operation) => {
                            pending.push(Walk::Leave(operation, Count(node.children.len())));
                            pending.extend(
                                node.children.iter().rev().map(|&child| Walk::Enter(child)),
                            );
                        },
                        TermHead::Var(_) => {
                            built.push(table.var(Variable::from(fresh)));
                            fresh = fresh.saturating_add(1);
                        },
                    }
                },
                Walk::Leave(operation, arity) => {
                    let start = built.len().checked_sub(arity.0)?;
                    let arguments = built.split_off(start);
                    built.push(table.op(operation, arguments).ok()?);
                },
            }
        }
        terms.push(built.pop()?);
    }
    Some(Arrow {
        source: Arity::from(fresh),
        terms,
    })
}

/// The arrows into `target` variables with one to `largest` operations whose
/// terms are linear normal forms, each variable numbered in pre-order.
///
/// # Specification
/// trivial.
fn linear_arrows(
    theory: &mut LawvereTheory,
    shapes: &[Vec<TermPlace>],
    (target, largest): (Arity, Count),
) -> Option<Vec<Arrow>>
{
    let mut out = Vec::new();
    let mut tuples: Vec<Vec<TermPlace>> = Vec::new();
    let mut longer: Vec<Vec<TermPlace>> = Vec::new();
    for total in 1 ..= largest.0 {
        for sizes in spread(Count(total), Count(usize::from(target))) {
            tuples.clear();
            tuples.push(Vec::new());
            for part in sizes {
                longer.clear();
                let terms = shapes.get(part.0).map_or(&[][..], Vec::as_slice);
                for tuple in &tuples {
                    for &term in terms {
                        let mut next = tuple.clone();
                        next.push(term);
                        longer.push(next);
                    }
                }
                core::mem::swap(&mut tuples, &mut longer);
            }
            while let Some(terms) = tuples.pop() {
                let holed = Arrow {
                    source: Arity::from(1_usize),
                    terms,
                };
                let arrow = numbered(theory.table_mut(), &holed)?;
                let mut normal = true;
                for &term in &arrow.terms {
                    normal = normal && theory.normal_form(term).ok()? == term;
                }
                if normal {
                    out.push(arrow);
                }
            }
        }
    }
    Some(out)
}

/// The essential cells of degrees one to [`DEGREES`], by degree. Each arrow
/// after the first of an essential cell is the top of a redex, so it has at
/// most as many operations as a rule's left side. None past the fuel.
///
/// # Specification
/// trivial.
fn essential(theory: &mut LawvereTheory) -> Option<Vec<Vec<BarCell>>>
{
    let mut largest = Count(0);
    for &(left, _) in theory.rules() {
        largest = largest.max(operations(theory.table(), left)?);
    }
    let hole = theory.table_mut().var(Variable::from(0_usize));
    let mut shapes: Vec<Vec<TermPlace>> = vec![vec![hole]];
    for size in 1 ..= largest.0 {
        let found = shapes_of(theory, &shapes, Count(size))?;
        shapes.push(found);
    }
    let mut generators = Vec::new();
    for place in 0 .. theory.arities().len() {
        let operation = Operation::from(place);
        let arity = theory.arities().get(place).copied().unwrap_or_default();
        generators.push(BarCell(vec![
            theory.table_mut().generator(operation, arity).ok()?,
        ]));
    }
    let mut out = vec![generators];
    while out.len() < DEGREES {
        let mut found = Vec::new();
        for cell in out.last()? {
            let target = cell.0.last()?.source;
            for arrow in linear_arrows(theory, &shapes, (target, largest))? {
                let mut arrows = cell.0.clone();
                arrows.push(arrow);
                let candidate = BarCell(arrows);
                if theory.class(&candidate).ok()? == Class::Critical {
                    found.push(candidate);
                }
            }
        }
        out.push(found);
    }
    Some(out)
}

/// The operation nodes of the term at `place`.
///
/// # Specification
/// trivial.
fn operations(
    table: &TermTable,
    place: TermPlace,
) -> Option<Count>
{
    let mut found = 0_usize;
    let mut pending = vec![place];
    while let Some(next) = pending.pop() {
        let node = table.node(next).ok()?;
        if let TermHead::Op(_) = node.head {
            found = found.saturating_add(1);
        }
        pending.extend(&node.children);
    }
    Some(Count(found))
}

/// An overlap of two rules: its peak, when the reading spells it, and the two
/// left sides, the lesser first.
type Overlap = (Option<TermPlace>, TermPlace, TermPlace);

/// The overlap of the rules at `left` and `right`, the lesser first.
///
/// # Specification
/// trivial.
fn overlap(
    peak: Option<TermPlace>,
    (left, right): (TermPlace, TermPlace),
) -> Overlap
{
    (peak, left.min(right), left.max(right))
}

/// What the collapse of one reading of a block gives.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Collapse
{
    /// The essential cells of degrees one to three.
    essential: [Count; DEGREES],
    /// The essential cells of degree two less the rules' left sides, and the
    /// left sides less those cells.
    rules: (Count, Count),
    /// The essential cells of degree three less the certified pairs, and the
    /// pairs less those cells.
    pairs: (Count, Count),
    /// The certified pairs of the commands reading that overlap a cell which
    /// is no rule, a frame cell or an eta cell. No essential cell answers one.
    frames: Count,
    /// The faults of the matching inside the bound.
    faults: Faults,
}

/// Whether a collapse gives the rules and the certified pairs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Verdict
{
    /// The essential cells are the rules and the pairs, and the matching has
    /// no fault.
    Holds,
    /// A cell, a rule or a pair stays unmatched, a pair overlaps a cell which
    /// is no rule, or the matching has a fault.
    Fails,
}

impl Collapse
{
    /// Whether the collapse gives the rules and the certified pairs.
    ///
    /// # Specification
    /// trivial.
    fn verdict(&self) -> Verdict
    {
        let none = Count(0);
        if self.rules == (none, none)
            && self.pairs == (none, none)
            && self.frames == none
            && self.faults == Faults::default()
        {
            Verdict::Holds
        }
        else {
            Verdict::Fails
        }
    }
}

/// The bound of the truncation the matching is checked on: two variables, and
/// a total size of five.
///
/// # Specification
/// trivial.
fn checked_bound() -> BarBound
{
    bound(Count(2), Count(5))
}

/// The differences of two multisets: the count of `left` less `right`, and
/// of `right` less `left`.
///
/// # Specification
/// trivial.
fn differences<Item>(
    left: &[Item],
    right: &[Item],
) -> (Count, Count)
where
    Item: Ord + Clone,
{
    let mut counts: BTreeMap<Item, i64> = BTreeMap::new();
    for item in left {
        let count = counts.entry(item.clone()).or_default();
        *count = count.saturating_add(1);
    }
    for item in right {
        let count = counts.entry(item.clone()).or_default();
        *count = count.saturating_sub(1);
    }
    let over = counts
        .values()
        .filter(|&&count| count > 0)
        .map(|&count| count.unsigned_abs());
    let under = counts
        .values()
        .filter(|&&count| count < 0)
        .map(|&count| count.unsigned_abs());
    let total = |counts: &mut dyn Iterator<Item = u64>| {
        Count(usize::try_from(counts.fold(0_u64, u64::saturating_add)).unwrap_or(usize::MAX))
    };
    (total(&mut { over }), total(&mut { under }))
}

/// Why the probe decides nothing on a reading of a block.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Undecided
{
    /// Completion refuses the block or does not examine it, so it certifies
    /// no pairs.
    Uncertified,
    /// A rule's term binds a variable, so the theory is not first-order.
    Binding,
    /// A rule's left side is a variable, or a variable occurs twice in it.
    Nonlinear,
    /// A rule changes the occurrences of a variable, so the theory refuses
    /// it.
    Unbalanced,
    /// A generator is not a normal form: a rule defines its operation.
    Defined,
    /// A normal form takes more than the fuel, the cycle check visits more
    /// than [`CLOSURE`] cells, or a certified pair does not read.
    Bound,
}

/// Whether each variable of a term occurs once.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Linearity
{
    /// Each variable occurs once.
    Linear,
    /// A variable occurs twice.
    Repeated,
}

/// The collapse of one reading of `cells`, or why the probe decides nothing
/// on it.
///
/// # Specification
/// trivial.
fn collapse(
    cells: &DeclarationCells,
    (reading, block): (Reading, &Presentation),
) -> Result<Collapse, Undecided>
{
    let certificates = certified(cells).ok_or(Undecided::Uncertified)?;
    let (mut theory, names) = presented(&block.rules).map_err(|unpresented| match unpresented {
        Unpresented::Unread => Undecided::Binding,
        Unpresented::Refused(LawvereError::Unbalanced(_)) => Undecided::Unbalanced,
        Unpresented::Refused(
            LawvereError::Exhausted(_)
            | LawvereError::Unissued(_)
            | LawvereError::Unfilled(_)
            | LawvereError::NoTerm
            | LawvereError::LeadingVariable
            | LawvereError::Overflow,
        ) => Undecided::Bound,
    })?;
    for &(left, _) in theory.rules() {
        if let TermHead::Var(_) = theory
            .table()
            .node(left)
            .map_err(|_fault| Undecided::Bound)?
            .head
        {
            return Err(Undecided::Nonlinear);
        }
        if linearity(theory.table(), left).ok_or(Undecided::Bound)? == Linearity::Repeated {
            return Err(Undecided::Nonlinear);
        }
    }
    for place in 0 .. theory.arities().len() {
        let operation = Operation::from(place);
        let arity = theory.arities().get(place).copied().unwrap_or_default();
        let generator = theory
            .table_mut()
            .generator(operation, arity)
            .map_err(|_fault| Undecided::Bound)?;
        let term = *generator.terms.first().ok_or(Undecided::Bound)?;
        if theory
            .normal_form(term)
            .map_err(|_fault| Undecided::Bound)?
            != term
        {
            return Err(Undecided::Defined);
        }
    }
    let found = essential(&mut theory).ok_or(Undecided::Bound)?;
    let lefts: Vec<TermPlace> = theory.rules().iter().map(|&(left, _)| left).collect();
    let spelled = spelled_cells(&mut theory, (&found, &lefts), reading).ok_or(Undecided::Bound)?;
    let (certified_overlaps, frames) = certified_overlaps(
        (&mut theory, &names),
        (reading, block),
        (&certificates, &lefts),
    )
    .ok_or(Undecided::Bound)?;
    let truncated = theory
        .truncation(checked_bound())
        .map_err(|_fault| Undecided::Bound)?;
    let faults = faults(&mut theory, &truncated).ok_or(Undecided::Bound)?;
    let mut essential = [Count(0); DEGREES];
    for (slot, cells) in essential.iter_mut().zip(&found) {
        *slot = Count(cells.len());
    }
    Ok(Collapse {
        essential,
        rules: differences(&spelled.0, &lefts),
        pairs: differences(&spelled.1, &certified_overlaps),
        frames,
        faults,
    })
}

/// The left sides that the essential cells of degree two spell, and the
/// overlaps that those of degree three spell. An overlap keeps its peak in
/// the terms reading only.
///
/// # Specification
/// trivial.
fn spelled_cells(
    theory: &mut LawvereTheory,
    (found, lefts): (&[Vec<BarCell>], &[TermPlace]),
    reading: Reading,
) -> Option<(Vec<TermPlace>, Vec<Overlap>)>
{
    let mut spelled_lefts = Vec::new();
    for cell in found.get(1)? {
        let (generator, top) = (cell.0.first()?, cell.0.get(1)?);
        spelled_lefts.push(
            theory
                .table_mut()
                .substituted(*generator.terms.first()?, &top.terms)
                .ok()?,
        );
    }
    let mut overlaps = Vec::new();
    for cell in found.get(2)? {
        let (generator, top, below) = (cell.0.first()?, cell.0.get(1)?, cell.0.get(2)?);
        let left = theory
            .table_mut()
            .substituted(*generator.terms.first()?, &top.terms)
            .ok()?;
        let peak = theory.table_mut().substituted(left, &below.terms).ok()?;
        let Maybe::Present(rule) = theory.overlapping(cell).ok()?
        else {
            return None;
        };
        let other = lefts.get(usize::from(rule)).copied()?;
        let peak = (reading == Reading::Terms).then_some(peak);
        overlaps.push(overlap(peak, (left, other)));
    }
    Some((spelled_lefts, overlaps))
}

/// The overlaps of the pairs that completion certifies in `reading`, and the
/// count of pairs of the commands reading that overlap a frame cell or an eta
/// cell. Neither cell is a rule, so such a pair is no overlap of two rules.
///
/// # Specification
/// trivial.
fn certified_overlaps(
    (theory, names): (&mut LawvereTheory, &[String]),
    (reading, block): (Reading, &Presentation),
    (certificates, lefts): (&Certificates, &[TermPlace]),
) -> Option<(Vec<Overlap>, Count)>
{
    let mut out = Vec::new();
    let mut frames = Count(0);
    match reading {
        Reading::Terms => {
            let mut variables = BTreeMap::new();
            for pair in &certificates.terms {
                let free = spelled(&pair.overlap.peak)?;
                variables.clear();
                let peak = read(
                    &free,
                    (names, theory.table_mut()),
                    (&mut variables, Side::Left),
                )?;
                let left = lefts.get(block.index.get(&pair.overlap.left)?.0).copied()?;
                let right = lefts
                    .get(block.index.get(&pair.overlap.right)?.0)
                    .copied()?;
                out.push(overlap(Some(peak), (left, right)));
            }
        },
        Reading::Commands => {
            for pair in &certificates.commands {
                let (Some(left), Some(right)) = (
                    block.index.get(&pair.overlap.left),
                    block.index.get(&pair.overlap.right),
                )
                else {
                    frames.0 = frames.0.saturating_add(1);
                    continue;
                };
                let left = lefts.get(left.0).copied()?;
                let right = lefts.get(right.0).copied()?;
                out.push(overlap(None, (left, right)));
            }
        },
    }
    Some((out, frames))
}

/// Whether each variable of the term at `place` occurs once.
///
/// # Specification
/// trivial.
fn linearity(
    table: &TermTable,
    place: TermPlace,
) -> Option<Linearity>
{
    let mut seen = BTreeSet::new();
    let mut pending = vec![place];
    while let Some(next) = pending.pop() {
        let node = table.node(next).ok()?;
        if let TermHead::Var(variable) = node.head
            && !seen.insert(variable)
        {
            return Some(Linearity::Repeated);
        }
        pending.extend(&node.children);
    }
    Some(Linearity::Linear)
}

/// The essential cell counts of a decided reading, and its verdict.
type Decision = Result<([Count; DEGREES], Verdict), Undecided>;

#[test]
fn the_essential_cells_of_nat_units_are_its_operations_rules_and_pairs()
{
    // The try-first of the unit. `NatUnits` has `Succ`, `Zero` and `add`, in
    // name order. Its rules are `add(Zero, n) ⇒ n`, `add(m, Zero) ⇒ m` and
    // `add(Succ(m), n) ⇒ Succ(add(m, n))`. The subscript of an arrow counts
    // the variables of its context. The essential cells are the three
    // generators, the three left sides, and the two overlaps
    // `add(Zero, Zero)` and `add(Succ(x₁), Zero)`.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let text = std::fs::read_to_string(root.join("model/desc/rules-overlap-joinable.gandr"))
        .expect("a corpus source reads");
    let source = SourceText::from(text.as_str());
    let mut theories = Vec::new();
    let _lowering = each_block(&grammar, source, |cells| {
        let named = source
            .fragment(cells.at.span)
            .map(|fragment| fragment.as_ref().starts_with("data NatUnits"));
        if matches!(named, Ok(true)) {
            theories.push(
                presented(&rules_of(cells, Reading::Commands)).expect("NatUnits is first-order"),
            );
        }
    });
    let Some((mut theory, names)) = theories.pop()
    else {
        panic!("the source holds NatUnits");
    };
    assert_eq!(names, ["Succ", "Zero", "add"]);
    let (succ, zero, add) = (
        Operation::from(0_usize),
        Operation::from(1_usize),
        Operation::from(2_usize),
    );
    let table = theory.table_mut();
    let (first, second) = (
        table.var(Variable::from(0_usize)),
        table.var(Variable::from(1_usize)),
    );
    let mut op = |operation: Operation, children: Vec<TermPlace>| {
        table.op(operation, children).expect("a term of NatUnits")
    };
    let nought = op(zero, Vec::new());
    let sum = op(add, vec![first, second]);
    let next = op(succ, vec![first]);
    let arrow = |source: usize, terms: &[TermPlace]| Arrow {
        source: Arity::from(source),
        terms: terms.to_vec(),
    };
    let cell = |arrows: &[Arrow]| BarCell(arrows.to_vec());
    let found = essential(&mut theory).expect("the essential cells build");
    let generators: BTreeSet<BarCell> = [
        cell(&[arrow(1, &[next])]),
        cell(&[arrow(0, &[nought])]),
        cell(&[arrow(2, &[sum])]),
    ]
    .into();
    let lefts: BTreeSet<BarCell> = [
        cell(&[arrow(2, &[sum]), arrow(1, &[nought, first])]),
        cell(&[arrow(2, &[sum]), arrow(1, &[first, nought])]),
        cell(&[arrow(2, &[sum]), arrow(2, &[next, second])]),
    ]
    .into();
    let overlaps: BTreeSet<BarCell> = [
        cell(&[
            arrow(2, &[sum]),
            arrow(1, &[first, nought]),
            arrow(0, &[nought]),
        ]),
        cell(&[
            arrow(2, &[sum]),
            arrow(2, &[next, second]),
            arrow(1, &[first, nought]),
        ]),
    ]
    .into();
    let by_degree: Vec<BTreeSet<BarCell>> = found.into_iter().map(BTreeSet::from_iter).collect();
    assert_eq!(by_degree, [generators, lefts, overlaps]);
}

#[test]
fn the_blocks_of_5258_collapse_onto_their_rules_and_certified_pairs()
{
    // `NatUnits` reads its rules over commands. Its essential cells are its
    // three generators, its three rules and its two certified pairs.
    // `NatAssoc` reads its rules over terms and over commands. Over terms,
    // associativity overlaps each of the three rules once. Over commands, two
    // rules stay and completion certifies no pair. Completion refuses
    // `NatApart`, so the probe decides nothing on it.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let mut found: Vec<(String, Option<Reading>, Decision)> = Vec::new();
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
            let Some(certificates) = certified(cells)
            else {
                found.push((String::from(block), None, Err(Undecided::Uncertified)));
                return;
            };
            for (reading, rules) in readings(cells, &certificates) {
                let rules = rules.expect("the block's rules spell free terms");
                let decision = collapse(cells, (reading, &rules))
                    .map(|collapsed| (collapsed.essential, collapsed.verdict()));
                found.push((String::from(block), Some(reading), decision));
            }
        });
    }
    let counts = |cells: [usize; DEGREES]| cells.map(Count);
    assert_eq!(found, [
        (
            String::from("data NatUnits"),
            Some(Reading::Commands),
            Ok((counts([3, 3, 2]), Verdict::Holds)),
        ),
        (
            String::from("data NatAssoc"),
            Some(Reading::Terms),
            Ok((counts([3, 3, 3]), Verdict::Holds)),
        ),
        (
            String::from("data NatAssoc"),
            Some(Reading::Commands),
            Ok((counts([3, 2, 0]), Verdict::Holds)),
        ),
        (
            String::from("data NatApart"),
            None,
            Err(Undecided::Uncertified),
        ),
    ]);
}

#[test]
fn every_decided_corpus_reading_collapses_onto_its_rules_and_certified_pairs_but_one()
{
    // Each reading that the probe decides has the rules as its essential cells
    // of degree two and the certified pairs as those of degree three. Its
    // matching has no fault. One reading fails. Over commands, completion
    // certifies a pair of `Wrap` that overlaps `unwrap(MkWrap(x)) ⇒ x` with the
    // eta cell of `Wrap`. The commands reading fires a cell only at a cut's
    // root, and the eta cell only at a cut of its polarity. The theory rewrites
    // at each position, so it cannot hold the eta cell as the commands reading
    // does. Without the cell, no essential cell answers the pair. With it, an
    // essential overlap answers no pair. The probe decides nothing on a reading
    // that binds, that repeats a variable on a left side, that changes the
    // occurrences of a variable, or that defines an operation by a rule.
    let grammar = built_in().expect("the built-in grammar builds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let mut decided = 0_usize;
    let mut bounded: Vec<String> = Vec::new();
    let mut failing: Vec<String> = Vec::new();
    for path in corpus() {
        let text = std::fs::read_to_string(&path).expect("a corpus source reads");
        let source = SourceText::from(text.as_str());
        let named = path.strip_prefix(&root).expect("a corpus path");
        let _lowering = each_block(&grammar, source, |cells| {
            let Some(certificates) = certified(cells)
            else {
                return;
            };
            for (reading, rules) in readings(cells, &certificates) {
                let Some(rules) = rules
                else {
                    continue;
                };
                if rules.rules.is_empty() {
                    continue;
                }
                match collapse(cells, (reading, &rules)) {
                    Ok(collapsed) => {
                        decided = decided.saturating_add(1);
                        if collapsed.verdict() == Verdict::Fails {
                            failing.push(format!("{}: {reading:?}", named.display()));
                        }
                    },
                    Err(Undecided::Bound) => {
                        bounded.push(format!("{}: {reading:?}", named.display()));
                    },
                    Err(
                        Undecided::Uncertified
                        | Undecided::Binding
                        | Undecided::Nonlinear
                        | Undecided::Unbalanced
                        | Undecided::Defined,
                    ) => {},
                }
            }
        });
    }
    assert!(decided > 1, "the corpus holds first-order blocks");
    assert!(
        bounded.is_empty(),
        "no reading passes the bound: {bounded:?}"
    );
    assert_eq!(failing, ["model/desc/desc-eta-cell.gandr: Commands"]);
}
