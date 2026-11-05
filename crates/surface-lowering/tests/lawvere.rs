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
use std::collections::HashMap;
use std::path::Path;

use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;

use crate::squier::Reading;
use crate::squier::certified;
use crate::squier::each_block;
use crate::squier::rules_of;
use crate::squier::small_complexes;

/// The place of an operation in a block's signature.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Operation(pub u8);

/// The place of a variable in a context.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable(pub u8);

/// A count: of variables, of arguments, of the nodes of a term, of cells.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Count(pub usize);

/// A coefficient of a chain.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Coefficient(pub i64);

/// A term's place in its table. Equal places are equal terms.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermId(u32);

/// The outermost symbol of a term.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Head
{
    /// A variable of the context.
    Var(Variable),
    /// An operation.
    Op(Operation),
}

/// One node of a term: its symbol and the places of its arguments.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Node
{
    /// The symbol.
    pub head: Head,
    /// The arguments, each interned before the node.
    pub children: Vec<TermId>,
}

/// The interned terms of one theory: each distinct term once, each after its
/// arguments.
#[derive(Debug, Default)]
pub struct Table
{
    /// The nodes, by place.
    nodes: Vec<Node>,
    /// The size of each term, by place.
    sizes: Vec<Count>,
    /// The place of each node.
    places: HashMap<Node, TermId>,
}

impl Table
{
    /// The place of `node`, interned once.
    ///
    /// # Specification
    /// trivial.
    pub fn intern(
        &mut self,
        node: Node,
    ) -> TermId
    {
        if let Some(&place) = self.places.get(&node) {
            return place;
        }
        let size = node
            .children
            .iter()
            .map(|&child| self.size(child).0)
            .fold(1, usize::saturating_add);
        let place = TermId(u32::try_from(self.nodes.len()).expect("a small table"));
        self.nodes.push(node.clone());
        self.sizes.push(Count(size));
        let _absent = self.places.insert(node, place);
        place
    }

    /// The variable `variable`.
    ///
    /// # Specification
    /// trivial.
    pub fn var(
        &mut self,
        variable: Variable,
    ) -> TermId
    {
        self.intern(Node {
            head: Head::Var(variable),
            children: Vec::new(),
        })
    }

    /// The operation `operation` applied to `children`.
    ///
    /// # Specification
    /// trivial.
    pub fn op(
        &mut self,
        operation: Operation,
        children: Vec<TermId>,
    ) -> TermId
    {
        self.intern(Node {
            head: Head::Op(operation),
            children,
        })
    }

    /// The node at `place`.
    ///
    /// # Specification
    /// trivial.
    pub fn node(
        &self,
        place: TermId,
    ) -> &Node
    {
        &self.nodes[usize::try_from(place.0).expect("a place")]
    }

    /// The nodes of the term at `place`, each variable and operation one.
    ///
    /// # Specification
    /// trivial.
    pub fn size(
        &self,
        place: TermId,
    ) -> Count
    {
        self.sizes[usize::try_from(place.0).expect("a place")]
    }

    /// The occurrences of each symbol in the term at `place`, each path from
    /// the root counted once.
    ///
    /// # Specification
    /// trivial.
    fn occurrences(
        &self,
        place: TermId,
    ) -> BTreeMap<Head, Count>
    {
        let mut counts: BTreeMap<Head, Count> = BTreeMap::new();
        let mut pending = vec![place];
        while let Some(next) = pending.pop() {
            let node = self.node(next);
            let count = counts.entry(node.head).or_default();
            count.0 = count.0.saturating_add(1);
            pending.extend(&node.children);
        }
        counts
    }

    /// The term at `place` with each variable `xⱼ` replaced by `values[j]`, or
    /// none when a variable has no value.
    ///
    /// # Specification
    /// trivial.
    pub fn substituted(
        &mut self,
        place: TermId,
        values: &[TermId],
    ) -> Option<TermId>
    {
        let mut done: HashMap<TermId, TermId> = HashMap::new();
        let mut pending = vec![(place, Visit::Enter)];
        while let Some((next, visit)) = pending.pop() {
            if done.contains_key(&next) {
                continue;
            }
            let head = self.node(next).head;
            match (head, visit) {
                (Head::Var(variable), _) => {
                    let _previous = done.insert(next, *values.get(usize::from(variable.0))?);
                },
                (Head::Op(_), Visit::Enter) => {
                    pending.push((next, Visit::Leave));
                    pending.extend(
                        self.node(next)
                            .children
                            .iter()
                            .rev()
                            .map(|&child| (child, Visit::Enter)),
                    );
                },
                (Head::Op(_), Visit::Leave) => {
                    let mut children = Vec::with_capacity(self.node(next).children.len());
                    for child in &self.node(next).children {
                        children.push(*done.get(child)?);
                    }
                    let substituted = self.intern(Node { head, children });
                    let _previous = done.insert(next, substituted);
                },
            }
        }
        done.get(&place).copied()
    }
}

/// Whether a walk enters a node or leaves it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// The walk reaches the node, before its arguments.
    Enter,
    /// The walk leaves the node, after its arguments.
    Leave,
}

/// Whether a match succeeds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Agreement
{
    /// The pattern matches.
    Agrees,
    /// The pattern does not match.
    Differs,
}

/// The Lawvere theory a convergent first-order block presents.
#[derive(Debug)]
pub struct Theory
{
    /// The arity of each operation.
    pub arities: Vec<Count>,
    /// The rules, each left side then right side, their variables numbered by
    /// their first occurrence on the left.
    pub rules: Vec<(TermId, TermId)>,
    /// The terms.
    pub table: Table,
    /// The normal forms found so far.
    normal: HashMap<TermId, TermId>,
}

/// The most rewrites one normal form takes before the probe gives up.
const FUEL: usize = 100_000;

impl Theory
{
    /// The theory of `arities` and `rules` over `table`.
    ///
    /// # Specification
    /// trivial.
    fn new(
        arities: Vec<Count>,
        rules: Vec<(TermId, TermId)>,
        table: Table,
    ) -> Self
    {
        Self {
            arities,
            rules,
            table,
            normal: HashMap::new(),
        }
    }

    /// Whether `pattern` matches the term at `place`, each variable of the
    /// pattern bound once in `binding`.
    ///
    /// # Specification
    /// trivial.
    fn matched(
        &self,
        (pattern, place): (TermId, TermId),
        binding: &mut BTreeMap<Variable, TermId>,
    ) -> Agreement
    {
        let mut pending = vec![(pattern, place)];
        while let Some((pattern, place)) = pending.pop() {
            let (want, have) = (self.table.node(pattern), self.table.node(place));
            match want.head {
                Head::Var(variable) => match binding.get(&variable) {
                    Some(&bound) if bound != place => return Agreement::Differs,
                    Some(_) => {},
                    None => {
                        let _previous = binding.insert(variable, place);
                    },
                },
                Head::Op(_) => {
                    if want.head != have.head || want.children.len() != have.children.len() {
                        return Agreement::Differs;
                    }
                    pending.extend(
                        want.children
                            .iter()
                            .copied()
                            .zip(have.children.iter().copied()),
                    );
                },
            }
        }
        Agreement::Agrees
    }

    /// The term that one rule rewrites the term at `place` to at its root.
    ///
    /// # Specification
    /// trivial.
    fn redex(
        &mut self,
        place: TermId,
    ) -> Option<TermId>
    {
        let mut binding = BTreeMap::new();
        let mut values = Vec::new();
        for index in 0 .. self.rules.len() {
            let (left, right) = self.rules[index];
            binding.clear();
            if self.matched((left, place), &mut binding) == Agreement::Agrees {
                values.clear();
                for count in 0 .. binding.len() {
                    values.push(*binding.get(&Variable(u8::try_from(count).ok()?))?);
                }
                return self.table.substituted(right, &values);
            }
        }
        None
    }

    /// The normal form of the term at `root`, innermost first, or none past
    /// the fuel.
    ///
    /// # Specification
    /// trivial.
    pub fn normal_form(
        &mut self,
        root: TermId,
    ) -> Option<TermId>
    {
        let mut fuel = Count(FUEL);
        let mut pending = vec![Task::Enter(root)];
        while let Some(task) = pending.pop() {
            match task {
                Task::Enter(place) => {
                    if self.normal.contains_key(&place) {
                        continue;
                    }
                    let head = self.table.node(place).head;
                    if let Head::Var(_) = head {
                        let _previous = self.normal.insert(place, place);
                        continue;
                    }
                    pending.push(Task::Leave(place));
                    pending.extend(
                        self.table
                            .node(place)
                            .children
                            .iter()
                            .rev()
                            .map(|&child| Task::Enter(child)),
                    );
                },
                Task::Leave(place) => {
                    if self.normal.contains_key(&place) {
                        continue;
                    }
                    let head = self.table.node(place).head;
                    let mut children = Vec::with_capacity(self.table.node(place).children.len());
                    for child in &self.table.node(place).children {
                        children.push(*self.normal.get(child)?);
                    }
                    let inner = self.table.intern(Node { head, children });
                    match self.redex(inner) {
                        None => {
                            let _previous = self.normal.insert(place, inner);
                            let _same = self.normal.insert(inner, inner);
                        },
                        Some(rewritten) => {
                            fuel.0 = fuel.0.checked_sub(1)?;
                            pending.push(Task::Await { place, rewritten });
                            pending.push(Task::Enter(rewritten));
                        },
                    }
                },
                Task::Await { place, rewritten } => {
                    let found = *self.normal.get(&rewritten)?;
                    let _previous = self.normal.insert(place, found);
                },
            }
        }
        self.normal.get(&root).copied()
    }

    /// The normal forms in `context` variables, by size, up to `largest`.
    ///
    /// # Specification
    /// trivial.
    fn normal_forms(
        &mut self,
        context: Count,
        largest: Count,
    ) -> Vec<Vec<TermId>>
    {
        let mut by_size: Vec<Vec<TermId>> = vec![Vec::new(); largest.0.saturating_add(1)];
        let mut tuples: Vec<Vec<TermId>> = Vec::new();
        let mut longer: Vec<Vec<TermId>> = Vec::new();
        for size in 1 ..= largest.0 {
            let mut found = Vec::new();
            if size == 1 {
                for place in 0 .. context.0 {
                    found.push(
                        self.table
                            .var(Variable(u8::try_from(place).expect("a small context"))),
                    );
                }
            }
            for place in 0 .. self.arities.len() {
                let operation = Operation(u8::try_from(place).expect("a small signature"));
                let arity = self.arities[place];
                for sizes in compositions(Count(size.saturating_sub(1)), arity) {
                    tuples.clear();
                    tuples.push(Vec::new());
                    for part in sizes {
                        longer.clear();
                        let arguments = by_size.get(part.0).map_or(&[][..], Vec::as_slice);
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
                        let term = self.table.op(operation, arguments);
                        if self.redex(term).is_none() {
                            found.push(term);
                        }
                    }
                }
            }
            by_size[size] = found;
        }
        by_size
    }
}

/// A unit of the normal-form walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Task
{
    /// Normalise the arguments of the term, then the term.
    Enter(TermId),
    /// The arguments have normal forms: rewrite the term at its root.
    Leave(TermId),
    /// The term rewrote to `rewritten`, whose normal form is the term's.
    Await
    {
        /// The term.
        place: TermId,
        /// What it rewrote to.
        rewritten: TermId,
    },
}

/// The ways to write `total` as an ordered sum of `parts` positive counts.
///
/// # Specification
/// trivial.
fn compositions(
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
        let after = parts.0.saturating_sub(prefix.len()).saturating_sub(1);
        for first in 1 ..= remaining.0.saturating_sub(after) {
            let mut next = prefix.clone();
            next.push(Count(first));
            pending.push((next, Count(remaining.0.saturating_sub(first))));
        }
    }
    out
}

/// A morphism of the theory: a tuple of normal forms in `source` variables.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arrow
{
    /// The variables of the context.
    pub source: Count,
    /// The terms, one for each variable of the tuple before.
    pub terms: Vec<TermId>,
}

/// A cell of the bar complex: a composable list of arrows, the first one term.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Cell(pub Vec<Arrow>);

/// Whether a cell counts zero.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Degeneracy
{
    /// The first term is a variable, or a later arrow is an identity.
    Degenerate,
    /// The cell is a generator.
    Proper,
}

impl Cell
{
    /// Whether the cell is degenerate in `table`.
    ///
    /// # Specification
    /// trivial.
    pub fn degeneracy(
        &self,
        table: &Table,
    ) -> Degeneracy
    {
        let Some((first, later)) = self.0.split_first()
        else {
            return Degeneracy::Proper;
        };
        let leading = first.terms.first().map(|&term| table.node(term).head);
        let identity = |arrow: &Arrow| {
            arrow.source.0 == arrow.terms.len()
                && arrow.terms.iter().enumerate().all(|(place, &term)| {
                    u8::try_from(place)
                        .is_ok_and(|place| table.node(term).head == Head::Var(Variable(place)))
                })
        };
        if matches!(leading, None | Some(Head::Var(_))) || later.iter().any(identity) {
            Degeneracy::Degenerate
        }
        else {
            Degeneracy::Proper
        }
    }

    /// The total size of the cell's terms in `table`.
    ///
    /// # Specification
    /// trivial.
    fn weight(
        &self,
        table: &Table,
    ) -> Count
    {
        Count(
            self.0
                .iter()
                .flat_map(|arrow| &arrow.terms)
                .map(|&term| table.size(term).0)
                .fold(0, usize::saturating_add),
        )
    }
}

/// A chain of the bar complex: cells with nonzero coefficients.
pub type Chain = BTreeMap<Cell, Coefficient>;

/// Add `coefficient` times `cell` to `chain`, a degenerate cell counting zero.
///
/// # Specification
/// trivial.
fn accumulate(
    (chain, table): (&mut Chain, &Table),
    cell: Cell,
    coefficient: Coefficient,
)
{
    if coefficient.0 == 0 || cell.degeneracy(table) == Degeneracy::Degenerate {
        return;
    }
    let entry = chain.entry(cell).or_default();
    entry.0 = entry.0.saturating_add(coefficient.0);
}

/// The boundary of `cell`, or none when a composite has no normal form within
/// the fuel.
///
/// # Specification
/// trivial.
pub fn boundary(
    theory: &mut Theory,
    cell: &Cell,
) -> Option<Chain>
{
    let mut chain = Chain::new();
    let arrows = &cell.0;
    let Some(first) = arrows.first()
    else {
        return Some(chain);
    };
    let occurrences: BTreeMap<Variable, Count> = theory
        .table
        .occurrences(*first.terms.first()?)
        .into_iter()
        .filter_map(|(head, count)| match head {
            Head::Var(variable) => Some((variable, count)),
            Head::Op(_) => None,
        })
        .collect();
    let degree = arrows.len();
    if degree == 1 {
        let total = occurrences
            .values()
            .map(|count| count.0)
            .fold(0, usize::saturating_add);
        let coefficient = Coefficient(i64::try_from(total).ok()?.saturating_sub(1));
        accumulate((&mut chain, &theory.table), Cell(Vec::new()), coefficient);
    }
    else {
        let second = arrows.get(1)?;
        for (variable, count) in &occurrences {
            let mut face = vec![Arrow {
                source: second.source,
                terms: vec![*second.terms.get(usize::from(variable.0))?],
            }];
            face.extend(arrows.iter().skip(2).cloned());
            let coefficient = Coefficient(i64::try_from(count.0).ok()?);
            accumulate((&mut chain, &theory.table), Cell(face), coefficient);
        }
        for inner in 1 .. degree {
            let (outer, filler) = (arrows.get(inner.saturating_sub(1))?, arrows.get(inner)?);
            let mut terms = Vec::with_capacity(outer.terms.len());
            for &term in &outer.terms {
                let composite = theory.table.substituted(term, &filler.terms)?;
                terms.push(theory.normal_form(composite)?);
            }
            let mut face: Vec<Arrow> = arrows
                .iter()
                .take(inner.saturating_sub(1))
                .cloned()
                .collect();
            face.push(Arrow {
                source: filler.source,
                terms,
            });
            face.extend(arrows.iter().skip(inner.saturating_add(1)).cloned());
            accumulate((&mut chain, &theory.table), Cell(face), sign(Count(inner)));
        }
        let last = Cell(
            arrows
                .iter()
                .take(degree.saturating_sub(1))
                .cloned()
                .collect(),
        );
        accumulate((&mut chain, &theory.table), last, sign(Count(degree)));
    }
    chain.retain(|_, coefficient| coefficient.0 != 0);
    Some(chain)
}

/// `(−1)ⁱ` for `i = index`.
///
/// # Specification
/// trivial.
const fn sign(index: Count) -> Coefficient
{
    if index.0 & 1 == 0 {
        Coefficient(1)
    }
    else {
        Coefficient(-1)
    }
}

/// The bound of a truncation: the variables of each arrow's context and the
/// total size of a cell's terms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bound
{
    /// The most variables in a context.
    pub variables: Count,
    /// The largest total size of a cell's terms.
    pub weight: Count,
}

/// The cells of the largest subcomplex inside a bound, by degree, with the
/// boundary of each.
#[derive(Debug, Default)]
pub struct Truncation
{
    /// The cells of each degree, in order.
    pub cells: Vec<Vec<Cell>>,
    /// The boundary of each cell.
    boundaries: HashMap<Cell, Chain>,
}

/// The highest degree the probe builds: three, so the homology of degree two
/// has its boundaries.
const TOP: usize = 3;

/// The largest subcomplex of degrees zero to three inside `bound`, or none when
/// a boundary has no normal form within the fuel.
///
/// # Specification
/// trivial.
pub fn truncation(
    theory: &mut Theory,
    bound: Bound,
) -> Option<Truncation>
{
    let mut forms: Vec<Vec<Vec<TermId>>> = Vec::with_capacity(bound.variables.0.saturating_add(1));
    for context in 0 ..= bound.variables.0 {
        forms.push(theory.normal_forms(Count(context), bound.weight));
    }
    let point = Cell(Vec::new());
    let mut out = Truncation {
        cells: vec![vec![point.clone()]],
        boundaries: HashMap::new(),
    };
    let _point = out.boundaries.insert(point.clone(), Chain::new());
    let mut previous: Vec<Cell> = vec![point];
    let mut candidates: Vec<Cell> = Vec::new();
    for _degree in 1 ..= TOP {
        candidates.clear();
        for cell in &previous {
            let target = cell.0.last().map_or(Count(1), |last| last.source);
            let room = Count(bound.weight.0.saturating_sub(cell.weight(&theory.table).0));
            for (context, sized) in forms.iter().enumerate() {
                for terms in tuples((sized, &theory.table), target, room) {
                    let mut arrows = cell.0.clone();
                    arrows.push(Arrow {
                        source: Count(context),
                        terms,
                    });
                    let candidate = Cell(arrows);
                    if candidate.degeneracy(&theory.table) == Degeneracy::Proper {
                        candidates.push(candidate);
                    }
                }
            }
        }
        let mut kept = Vec::new();
        while let Some(candidate) = candidates.pop() {
            let chain = boundary(theory, &candidate)?;
            if chain.keys().all(|face| out.boundaries.contains_key(face)) {
                let _previous = out.boundaries.insert(candidate.clone(), chain);
                kept.push(candidate);
            }
        }
        kept.sort();
        previous.clone_from(&kept);
        out.cells.push(kept);
    }
    Some(out)
}

/// The tuples of `length` normal forms from `sized`, listed by size in
/// `table`, whose sizes sum to at most `room`.
///
/// # Specification
/// trivial.
fn tuples(
    (sized, table): (&[Vec<TermId>], &Table),
    length: Count,
    room: Count,
) -> Vec<Vec<TermId>>
{
    let mut out: Vec<(Vec<TermId>, Count)> = vec![(Vec::new(), Count(0))];
    let mut longer: Vec<(Vec<TermId>, Count)> = Vec::new();
    for _ in 0 .. length.0 {
        longer.clear();
        for &(ref tuple, used) in &out {
            for forms in sized.iter().skip(1) {
                for &form in forms {
                    let total = used.0.saturating_add(table.size(form).0);
                    if total > room.0 {
                        continue;
                    }
                    let mut next = tuple.clone();
                    next.push(form);
                    longer.push((next, Count(total)));
                }
            }
        }
        core::mem::swap(&mut out, &mut longer);
    }
    out.into_iter().map(|(tuple, _)| tuple).collect()
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
    (large, table): (&Truncation, &Table),
    small: Bound,
    prime: Prime,
) -> Option<[Count; TOP]>
{
    let index: Vec<BTreeMap<&Cell, Count>> = large
        .cells
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
        let cells = large.cells.get(degree)?;
        let rows = index.get(degree)?;
        // The cycles among the cells inside the small bound.
        kernel.clear();
        cycles.clear();
        for cell in cells
            .iter()
            .filter(|cell| cell.weight(table).0 <= small.weight.0)
        {
            let place = *rows.get(cell)?;
            let image = if degree == 0 {
                Sparse::new()
            }
            else {
                vector(degree.saturating_sub(1), large.boundaries.get(cell)?)?
            };
            if let Some(cycle) = kernel.insert(prime, image, Sparse::from([(place, Residue(1))])) {
                cycles.push(cycle);
            }
        }
        // The boundaries from the large bound, then the cycles beside them.
        spanned.clear();
        for cell in large.cells.get(degree.saturating_add(1))? {
            let image = vector(degree, large.boundaries.get(cell)?)?;
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
    theory: &mut Theory,
    (small, large): (Bound, Bound),
) -> Option<Bar>
{
    let truncation = truncation(theory, large)?;
    let [first, second] =
        PRIMES.map(|prime| persistent((&truncation, &theory.table), small, prime));
    let homology = first?;
    assert_eq!(Some(homology), second, "the ranks agree modulo both primes");
    let mut cells = [Count(0); TOP + 1];
    for (slot, found) in cells.iter_mut().zip(&truncation.cells) {
        *slot = Count(found.len());
    }
    Some(Bar { homology, cells })
}

/// The cells of degrees two and three inside `bound` whose boundary has a
/// nonzero boundary.
///
/// # Specification
/// trivial.
fn unclosed(
    theory: &mut Theory,
    bound: Bound,
) -> Vec<Cell>
{
    let truncation = truncation(theory, bound).expect("the truncation builds");
    let mut out = Vec::new();
    let mut total = Chain::new();
    for cell in truncation.cells.iter().skip(2).flatten() {
        total.clear();
        for (face, coefficient) in &truncation.boundaries[cell] {
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
pub fn presented(rules: &[(FreeTerm, FreeTerm)]) -> Option<(Theory, Vec<String>)>
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
    let mut table = Table::default();
    let mut out = Vec::with_capacity(rules.len());
    let mut variables: BTreeMap<String, Variable> = BTreeMap::new();
    for &(ref left, ref right) in rules {
        variables.clear();
        let left = read(left, (&names, &mut table), (&mut variables, Side::Left))?;
        let right = read(right, (&names, &mut table), (&mut variables, Side::Right))?;
        out.push((left, right));
    }
    Some((
        Theory::new(arities.into_values().collect(), out, table),
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
    (names, table): (&[String], &mut Table),
    (variables, side): (&mut BTreeMap<String, Variable>, Side),
) -> Option<TermId>
{
    let mut walk: Vec<Walk<'_>> = Vec::new();
    let mut arguments: Vec<TermNode<'_>> = Vec::new();
    let mut built: Vec<TermId> = Vec::new();
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
                    built.push(table.op(operation, children));
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
                let next = Variable(u8::try_from(variables.len()).ok()?);
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
                let operation = Operation(u8::try_from(place).ok()?);
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

/// The homology of degrees zero and one that the small complex gives once
/// each operation has the boundary `arity − 1`: one point, the operations,
/// and each rule's operations on its right side less those on its left.
///
/// # Specification
/// trivial.
fn with_operation_boundaries(theory: &Theory) -> [Count; 2]
{
    let prime = PRIMES[0];
    let mut operations = Echelon::default();
    for arity in &theory.arities {
        let difference = Coefficient(i64::try_from(arity.0).unwrap_or(i64::MAX).saturating_sub(1));
        let mut column = Sparse::new();
        if difference.0 != 0 {
            let _previous = column.insert(Count(0), prime.residue(difference));
        }
        let _vanishing = operations.insert(prime, column, Sparse::new());
    }
    let mut rules = Echelon::default();
    for &(left, right) in &theory.rules {
        let (left, right) = (
            theory.table.occurrences(left),
            theory.table.occurrences(right),
        );
        let mut column = Sparse::new();
        for place in 0 .. theory.arities.len() {
            let head = Head::Op(Operation(u8::try_from(place).unwrap_or(u8::MAX)));
            let count = |counts: &BTreeMap<Head, Count>| {
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
                .arities
                .len()
                .saturating_sub(operations.rank().0)
                .saturating_sub(rules.rank().0),
        ),
    ]
}

/// The bounds of the probe: two variables, cycles of total size four, and
/// boundaries of total size six.
const BOUNDS: (Bound, Bound) = (
    Bound {
        variables: Count(2),
        weight: Count(4),
    },
    Bound {
        variables: Count(2),
        weight: Count(6),
    },
);

/// The bounds one size smaller, to show the homology is stable.
const SMALLER: (Bound, Bound) = (
    Bound {
        variables: Count(2),
        weight: Count(3),
    },
    Bound {
        variables: Count(2),
        weight: Count(5),
    },
);

/// The theory of `arities` with no rule.
///
/// # Specification
/// trivial.
fn free(arities: &[Count]) -> Theory
{
    Theory::new(arities.to_vec(), Vec::new(), Table::default())
}

/// The circle: `Loop` and `Unloop`, each the other's inverse.
///
/// # Specification
/// trivial.
fn circle() -> Theory
{
    let (looped, unlooped) = (Operation(0), Operation(1));
    let mut table = Table::default();
    let x = table.var(Variable(0));
    let (unloop_x, loop_x) = (table.op(unlooped, vec![x]), table.op(looped, vec![x]));
    let rules = vec![
        (table.op(looped, vec![unloop_x]), x),
        (table.op(unlooped, vec![loop_x]), x),
    ];
    Theory::new(vec![Count(1), Count(1)], rules, table)
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
    let (succ, zero, add) = (Operation(0), Operation(1), Operation(2));
    let table = &mut theory.table;
    let (x, y) = (table.var(Variable(0)), table.var(Variable(1)));
    let constant = table.op(zero, Vec::new());
    let terms = [
        (0, table.op(zero, Vec::new()), -1),
        (0, table.op(succ, vec![constant]), -1),
        (1, table.op(succ, vec![x]), 0),
        (2, table.op(add, vec![x, y]), 1),
        (2, table.op(add, vec![x, x]), 1),
        (2, table.op(add, vec![y, x]), 1),
    ];
    let truncation = truncation(theory, Bound {
        variables: Count(2),
        weight: Count(3),
    })
    .expect("the cells build");
    let degree_one: BTreeSet<&Cell> = truncation
        .cells
        .get(1)
        .expect("cells of degree one")
        .iter()
        .collect();
    let point = Cell(Vec::new());
    for &(source, term, expected) in &terms {
        let held = Cell(vec![Arrow {
            source: Count(source),
            terms: vec![term],
        }]);
        assert!(degree_one.contains(&held), "{held:?} is a cell");
        let chain = &truncation.boundaries[&held];
        let found = chain.get(&point).copied().unwrap_or_default();
        assert_eq!(found, Coefficient(expected), "{held:?}");
    }
    // Contexts of zero, one and two variables hold 3, 6 and 11 such terms.
    assert_eq!(degree_one.len(), 20);
    assert!(degree_one.iter().all(|cell| {
        truncation.boundaries[*cell]
            .keys()
            .all(|face| *face == point)
    }));
}

#[test]
fn free_theories_and_the_circle_have_their_known_homology()
{
    // A free unary operation presents the free monoid on one letter, and the
    // circle presents the integers: both have the homology `1, 1, 0`. A free
    // binary operation and a free constant each bound the point, `2 − 1 = 1`
    // and `0 − 1 = −1`, so their homology is `0, 0, 0`.
    let homology = |theory: &mut Theory| bar(theory, BOUNDS).expect("the complex builds").homology;
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
    let bound = Bound {
        variables: Count(2),
        weight: Count(5),
    };
    assert!(unclosed(&mut circle(), bound).is_empty());
    let (disjunction, truth) = (Operation(0), Operation(1));
    let mut table = Table::default();
    let (x, constant) = (table.var(Variable(0)), table.op(truth, Vec::new()));
    let rules = vec![
        (table.op(disjunction, vec![constant, x]), constant),
        (table.op(disjunction, vec![x, constant]), constant),
    ];
    let mut erasing = Theory::new(vec![Count(2), Count(0)], rules, table);
    assert!(!unclosed(&mut erasing, bound).is_empty());
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
                unclosed(&mut theory, SMALLER.1).is_empty(),
                "{block} closes"
            );
            let stable = bar(&mut theory, SMALLER).expect("the smaller complex builds");
            let complex = bar(&mut theory, BOUNDS).expect("the complex builds");
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
