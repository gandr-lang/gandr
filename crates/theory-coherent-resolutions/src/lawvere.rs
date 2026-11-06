//! The bar complex of the Lawvere theory that a first-order rule block
//! presents.
//!
//! A first-order rule block presents a Lawvere theory. A morphism from `m` to
//! `k` is a tuple of `k` terms in `m` variables, and composition substitutes.
//! A convergent block gives each morphism one tuple of normal forms. With
//! trivial coefficients, an operation of arity `a` has the boundary `a − 1`.
//!
//! A cell of degree `n` is a composable list `[u₁|u₂|…|uₙ]` of tuples of
//! normal forms in context. The tuple `u₁` holds one term. Each later tuple
//! fills the variables of the tuple before it. A cell is degenerate when `u₁`
//! is a variable or a later tuple is an identity. A degenerate cell counts
//! zero.
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
//! The complex is infinite. [`LawvereTheory`] states the faces of a cell when
//! a caller asks, as a [`Complex`] of the Morse crate. A [`Truncation`] lists
//! the largest subcomplex inside a [`BarBound`].

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Standing;
use quenchant_shape::shape::Maybe;

use crate::boundary::Arity;
use crate::boundary::BarDegree;
use crate::boundary::NormalizationBudget;
use crate::boundary::Occurrences;
use crate::boundary::Operation;
use crate::boundary::TermPlace;
use crate::boundary::TermSize;
use crate::boundary::Variable;

/// The outermost symbol of a term.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermHead
{
    /// A variable of the context.
    Var(Variable),
    /// An operation.
    Op(Operation),
}

/// One node of a term: its symbol and the places of its arguments.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermNode
{
    /// The symbol.
    pub head: TermHead,
    /// The arguments, each interned before the node.
    pub children: Vec<TermPlace>,
}

/// Why a Lawvere theory or its bar complex gives no answer.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LawvereError
{
    /// The normal form of the term at this place takes more rewrites than
    /// the theory's budget.
    Exhausted(TermPlace),
    /// The table holds no term at this place.
    Unissued(TermPlace),
    /// A term names this variable, and the tuple that fills the term holds no
    /// term for it.
    Unfilled(Variable),
    /// The first arrow of a cell holds no term.
    NoTerm,
    /// A coefficient passes the integers that an incidence holds.
    Overflow,
}

impl fmt::Display for LawvereError
{
    /// The refusal in words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Exhausted(place) => write!(
                formatter,
                "the normal form of the term at place {} takes more rewrites than the budget",
                usize::from(place)
            ),
            Self::Unissued(place) => write!(
                formatter,
                "the table holds no term at place {}",
                usize::from(place)
            ),
            Self::Unfilled(variable) => write!(
                formatter,
                "the tuple that fills a term holds no term for its variable {}",
                usize::from(variable)
            ),
            Self::NoTerm => formatter.write_str("the first arrow of the cell holds no term"),
            Self::Overflow => {
                formatter.write_str("a coefficient passes the integers that an incidence holds")
            },
        }
    }
}

impl core::error::Error for LawvereError
{
}

/// The interned terms of one theory: each distinct term once, each after its
/// arguments.
#[derive(Clone, Debug, Default)]
pub struct TermTable
{
    /// The nodes, by place.
    nodes: Vec<TermNode>,
    /// The size of each term, by place.
    sizes: Vec<TermSize>,
    /// The place of each node.
    places: BTreeMap<TermNode, TermPlace>,
}

impl TermTable
{
    /// The place of `node`, interned once.
    ///
    /// # Specification
    /// - ensures: an equal node gives the same place, and a new node takes the
    ///   next place. The size of the term is one more than the sizes of its
    ///   arguments.
    /// - fails: [`LawvereError::Unissued`] when the table holds no term at a
    ///   place that `node` names as an argument.
    /// - panics: none.
    /// - executable: none — the ensures compares the result with the table
    ///   before the call, which the call changes.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: an argument of `node` is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one term interned twice, a term over it and an
    ///   argument from no table separate the three outcomes.
    /// - witness: `tests::lawvere::a_term_is_interned_once_after_its_arguments`
    #[inline]
    pub fn intern(
        &mut self,
        node: TermNode,
    ) -> Result<TermPlace, LawvereError>
    {
        if let Some(&place) = self.places.get(&node) {
            return Ok(place);
        }
        let mut size = TermSize::from(1_usize);
        for &child in &node.children {
            size = TermSize::from(usize::from(size).saturating_add(usize::from(self.size(child)?)));
        }
        Ok(self.insert(node, size))
    }

    /// Keep `node`, which the table does not hold, at the next place.
    ///
    /// # Specification
    /// trivial.
    fn insert(
        &mut self,
        node: TermNode,
        size: TermSize,
    ) -> TermPlace
    {
        let place = TermPlace::from(self.nodes.len());
        self.nodes.push(node.clone());
        self.sizes.push(size);
        let _absent = self.places.insert(node, place);
        place
    }

    /// The variable `variable`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn var(
        &mut self,
        variable: Variable,
    ) -> TermPlace
    {
        let node = TermNode {
            head: TermHead::Var(variable),
            children: Vec::new(),
        };
        if let Some(&place) = self.places.get(&node) {
            return place;
        }
        self.insert(node, TermSize::from(1_usize))
    }

    /// The operation `operation` applied to `children`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: a child is not in the table.
    #[inline]
    pub fn op(
        &mut self,
        operation: Operation,
        children: Vec<TermPlace>,
    ) -> Result<TermPlace, LawvereError>
    {
        self.intern(TermNode {
            head: TermHead::Op(operation),
            children,
        })
    }

    /// The node at `place`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: the table holds no term at `place`.
    #[inline]
    pub fn node(
        &self,
        place: TermPlace,
    ) -> Result<&TermNode, LawvereError>
    {
        self.nodes
            .get(usize::from(place))
            .ok_or(LawvereError::Unissued(place))
    }

    /// The nodes of the term at `place`, each variable and operation one.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: the table holds no term at `place`.
    #[inline]
    pub fn size(
        &self,
        place: TermPlace,
    ) -> Result<TermSize, LawvereError>
    {
        self.sizes
            .get(usize::from(place))
            .copied()
            .ok_or(LawvereError::Unissued(place))
    }

    /// Put into `counts` the occurrences of each variable in the term at
    /// `place`, each path from the root counted once.
    ///
    /// # Specification
    /// - ensures: `counts` holds exactly the variables of the term, each with
    ///   the number of its paths from the root.
    /// - fails: [`LawvereError::Unissued`] when the table holds no term at a
    ///   place that the walk reaches.
    /// - panics: none.
    /// - executable: none — the ensures counts paths, and the call holds no
    ///   second walk to check it against.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: the term is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term that shares one argument twice counts each
    ///   path, so a count of distinct nodes differs.
    /// - witness: `tests::lawvere::occurrences_count_each_path_from_the_root`
    #[inline]
    pub fn occurrences(
        &self,
        place: TermPlace,
        counts: &mut BTreeMap<Variable, Occurrences>,
    ) -> Result<(), LawvereError>
    {
        counts.clear();
        let mut pending = vec![place];
        while let Some(next) = pending.pop() {
            let node = self.node(next)?;
            match node.head {
                TermHead::Var(variable) => {
                    let count = counts.entry(variable).or_default();
                    *count = Occurrences::from(usize::from(*count).saturating_add(1));
                },
                TermHead::Op(_) => pending.extend(node.children.iter().copied()),
            }
        }
        Ok(())
    }

    /// The term at `place` with each variable `xⱼ` replaced by `values[j]`.
    ///
    /// # Specification
    /// - ensures: the result is the term with each variable replaced, and a
    ///   shared argument is replaced once.
    /// - fails: [`LawvereError::Unfilled`] when the term names a variable past
    ///   `values`; [`LawvereError::Unissued`] when the table holds no term at a
    ///   place that the walk reaches.
    /// - panics: none.
    /// - executable: none — the ensures states the term that substitution
    ///   builds, and the call holds no second substitution to check it against.
    ///
    /// # Errors
    /// - [`LawvereError::Unfilled`]: a variable has no value.
    /// - [`LawvereError::Unissued`]: the term is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term in two variables filled by two terms, and
    ///   filled by one, separate the filled and the unfilled cases.
    /// - witness: `tests::lawvere::substitution_fills_each_variable_and_refuses_an_unfilled_one`
    #[inline]
    pub fn substituted(
        &mut self,
        place: TermPlace,
        values: &[TermPlace],
    ) -> Result<TermPlace, LawvereError>
    {
        let mut done: BTreeMap<TermPlace, TermPlace> = BTreeMap::new();
        let mut pending = vec![(place, Visit::Enter)];
        while let Some((next, visit)) = pending.pop() {
            if done.contains_key(&next) {
                continue;
            }
            let head = self.node(next)?.head;
            match (head, visit) {
                (TermHead::Var(variable), Visit::Enter | Visit::Leave) => {
                    let value = values
                        .get(usize::from(variable))
                        .copied()
                        .ok_or(LawvereError::Unfilled(variable))?;
                    let _previous = done.insert(next, value);
                },
                (TermHead::Op(_), Visit::Enter) => {
                    pending.push((next, Visit::Leave));
                    pending.extend(
                        self.node(next)?
                            .children
                            .iter()
                            .rev()
                            .map(|&child| (child, Visit::Enter)),
                    );
                },
                (TermHead::Op(_), Visit::Leave) => {
                    let node = self.node(next)?;
                    let mut children = Vec::with_capacity(node.children.len());
                    for &child in &node.children {
                        children.push(*done.get(&child).ok_or(LawvereError::Unissued(child))?);
                    }
                    let substituted = self.intern(TermNode { head, children })?;
                    let _previous = done.insert(next, substituted);
                },
            }
        }
        done.get(&place)
            .copied()
            .ok_or(LawvereError::Unissued(place))
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

/// Whether a pattern matches a term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Agreement
{
    /// The pattern matches.
    Agrees,
    /// The pattern does not match.
    Differs,
}

quenchant_shape::reason_enum! {
    /// Why no rule rewrites a term at its root.
    pub mod root_rewrite {
        /// The reason no rewrite is found.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No rule's left side matches the term at its root.
            NoRule,
        }
    }
}

/// The Lawvere theory that a convergent first-order block presents, with the
/// normal forms that it finds so far.
#[derive(Clone, Debug)]
pub struct LawvereTheory
{
    /// The arity of each operation.
    arities: Vec<Arity>,
    /// The rules, each left side then right side. The variables of a rule
    /// take their places by their first occurrence on the left.
    rules: Vec<(TermPlace, TermPlace)>,
    /// The terms.
    table: TermTable,
    /// The normal forms found so far.
    normal: BTreeMap<TermPlace, TermPlace>,
    /// The most rewrites that one normal form takes.
    budget: NormalizationBudget,
}

impl LawvereTheory
{
    /// The theory of `arities` and `rules` over `table`, each normal form
    /// within `budget` rewrites.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        arities: Vec<Arity>,
        rules: Vec<(TermPlace, TermPlace)>,
        table: TermTable,
        budget: NormalizationBudget,
    ) -> Self
    {
        Self {
            arities,
            rules,
            table,
            normal: BTreeMap::new(),
            budget,
        }
    }

    /// The arity of each operation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arities(&self) -> &[Arity]
    {
        &self.arities
    }

    /// The rules, each left side then right side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[(TermPlace, TermPlace)]
    {
        &self.rules
    }

    /// The terms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn table(&self) -> &TermTable
    {
        &self.table
    }

    /// The terms, to intern more. A place keeps its term, so the normal forms
    /// found so far stay true.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn table_mut(&mut self) -> &mut TermTable
    {
        &mut self.table
    }

    /// Whether `pattern` matches the term at `place`, each variable of the
    /// pattern bound once in `binding`.
    ///
    /// # Specification
    /// trivial.
    fn matched(
        &self,
        (pattern, place): (TermPlace, TermPlace),
        binding: &mut BTreeMap<Variable, TermPlace>,
    ) -> Result<Agreement, LawvereError>
    {
        let mut pending = vec![(pattern, place)];
        while let Some((pattern, place)) = pending.pop() {
            let want = self.table.node(pattern)?;
            match want.head {
                TermHead::Var(variable) => match binding.get(&variable) {
                    Some(&bound) if bound != place => return Ok(Agreement::Differs),
                    Some(_) => {},
                    None => {
                        let _previous = binding.insert(variable, place);
                    },
                },
                TermHead::Op(_) => {
                    let have = self.table.node(place)?;
                    if want.head != have.head || want.children.len() != have.children.len() {
                        return Ok(Agreement::Differs);
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
        Ok(Agreement::Agrees)
    }

    /// The term that the first rule whose left side matches rewrites the term
    /// at `place` to, at its root.
    ///
    /// # Specification
    /// - ensures: the rules are read in their order, and the first whose left
    ///   side matches gives its right side under the match.
    /// - provides: [`root_rewrite::Absent::NoRule`] when no left side matches
    ///   the term at its root.
    /// - fails: [`LawvereError::Unfilled`] when the right side names a variable
    ///   that the left side does not bind; [`LawvereError::Unissued`] when a
    ///   place is not in the table.
    /// - panics: none.
    /// - executable: none — the ensures reads each rule in order, and the call
    ///   holds no second reading to check it against.
    ///
    /// # Errors
    /// - [`LawvereError::Unfilled`]: the rule's right side has a variable that
    ///   its left side does not bind.
    /// - [`LawvereError::Unissued`]: a place is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term that a rule rewrites and a term in normal form
    ///   separate the two outcomes.
    /// - witness: `tests::lawvere::a_normal_form_rewrites_innermost_first_within_its_budget`
    #[inline]
    pub fn redex(
        &mut self,
        place: TermPlace,
    ) -> Result<Maybe<TermPlace, root_rewrite::Absent>, LawvereError>
    {
        let mut binding = BTreeMap::new();
        let mut values = Vec::new();
        for index in 0 .. self.rules.len() {
            let Some(&(left, right)) = self.rules.get(index)
            else {
                break;
            };
            binding.clear();
            if self.matched((left, place), &mut binding)? == Agreement::Agrees {
                values.clear();
                for (&variable, &term) in &binding {
                    if usize::from(variable) != values.len() {
                        break;
                    }
                    values.push(term);
                }
                return self.table.substituted(right, &values).map(Maybe::Present);
            }
        }
        Ok(Maybe::Absent(root_rewrite::Absent::NoRule))
    }

    /// The normal form of the term at `root`, innermost first.
    ///
    /// # Specification
    /// - ensures: the result is in normal form, and the theory keeps it for
    ///   each term that the walk reaches.
    /// - fails: [`LawvereError::Exhausted`] when the walk takes more rewrites
    ///   than the budget; [`LawvereError::Unissued`] and
    ///   [`LawvereError::Unfilled`] as [`LawvereTheory::redex`] fails.
    /// - panics: none.
    /// - executable: none — the ensures is a statement about each rule at each
    ///   node of the result, which the call reads only once.
    /// - intension: one walk with an explicit stack. A term that the theory
    ///   holds a normal form for costs one lookup.
    ///
    /// # Errors
    /// - [`LawvereError::Exhausted`]: the budget runs out.
    /// - [`LawvereError::Unissued`]: a place is not in the table.
    /// - [`LawvereError::Unfilled`]: a rule's right side has a variable that
    ///   its left side does not bind.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term with a redex below a redex rewrites the inner
    ///   one first, and a rule that loops runs out of its budget.
    /// - witness: `tests::lawvere::a_normal_form_rewrites_innermost_first_within_its_budget`
    #[inline]
    pub fn normal_form(
        &mut self,
        root: TermPlace,
    ) -> Result<TermPlace, LawvereError>
    {
        let mut fuel = usize::from(self.budget);
        let mut pending = vec![Task::Enter(root)];
        while let Some(task) = pending.pop() {
            match task {
                Task::Enter(place) => {
                    if self.normal.contains_key(&place) {
                        continue;
                    }
                    let node = self.table.node(place)?;
                    match node.head {
                        TermHead::Var(_) => {
                            let _previous = self.normal.insert(place, place);
                        },
                        TermHead::Op(_) => {
                            pending.push(Task::Leave(place));
                            pending.extend(
                                node.children.iter().rev().map(|&child| Task::Enter(child)),
                            );
                        },
                    }
                },
                Task::Leave(place) => {
                    if self.normal.contains_key(&place) {
                        continue;
                    }
                    let node = self.table.node(place)?;
                    let head = node.head;
                    let mut children = Vec::with_capacity(node.children.len());
                    for &child in &node.children {
                        children.push(
                            *self
                                .normal
                                .get(&child)
                                .ok_or(LawvereError::Unissued(child))?,
                        );
                    }
                    let inner = self.table.intern(TermNode { head, children })?;
                    match self.redex(inner)? {
                        Maybe::Absent(root_rewrite::Absent::NoRule) => {
                            let _previous = self.normal.insert(place, inner);
                            let _same = self.normal.insert(inner, inner);
                        },
                        Maybe::Present(rewritten) => {
                            fuel = fuel.checked_sub(1).ok_or(LawvereError::Exhausted(root))?;
                            pending.push(Task::Await { place, rewritten });
                            pending.push(Task::Enter(rewritten));
                        },
                    }
                },
                Task::Await { place, rewritten } => {
                    let found = *self
                        .normal
                        .get(&rewritten)
                        .ok_or(LawvereError::Exhausted(root))?;
                    let _previous = self.normal.insert(place, found);
                },
            }
        }
        self.normal
            .get(&root)
            .copied()
            .ok_or(LawvereError::Unissued(root))
    }

    /// The normal forms in `context` variables, by size, up to `largest`.
    ///
    /// # Specification
    /// - ensures: the entry at each size lists each normal form of that size
    ///   once. The entry at size zero is empty.
    /// - fails: [`LawvereError::Unissued`] and [`LawvereError::Unfilled`] as
    ///   [`LawvereTheory::redex`] fails.
    /// - panics: none.
    /// - executable: none — the ensures is a statement about each term of each
    ///   size, which the call builds only once.
    /// - intension: the terms of a size take their arguments from the normal
    ///   forms of smaller sizes, so each term is built once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the truncation of a theory with a rule holds no term
    ///   that the rule rewrites.
    /// - witness: `tests::lawvere::the_boundary_of_each_boundary_in_a_truncation_is_zero`
    fn normal_forms(
        &mut self,
        context: Arity,
        largest: TermSize,
    ) -> Result<Vec<Vec<TermPlace>>, LawvereError>
    {
        let largest = usize::from(largest);
        let mut by_size: Vec<Vec<TermPlace>> = vec![Vec::new(); largest.saturating_add(1)];
        let mut tuples: Vec<Vec<TermPlace>> = Vec::new();
        let mut longer: Vec<Vec<TermPlace>> = Vec::new();
        for size in 1 ..= largest {
            let mut found = Vec::new();
            if size == 1 {
                for place in 0 .. usize::from(context) {
                    found.push(self.table.var(Variable::from(place)));
                }
            }
            for place in 0 .. self.arities.len() {
                let Some(&arity) = self.arities.get(place)
                else {
                    break;
                };
                for sizes in compositions(TermSize::from(size.saturating_sub(1)), arity) {
                    tuples.clear();
                    tuples.push(Vec::new());
                    for part in sizes {
                        longer.clear();
                        let arguments = by_size
                            .get(usize::from(part))
                            .map_or(&[][..], Vec::as_slice);
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
                        let term = self.table.op(Operation::from(place), arguments)?;
                        match self.redex(term)? {
                            Maybe::Absent(root_rewrite::Absent::NoRule) => found.push(term),
                            Maybe::Present(_) => {},
                        }
                    }
                }
            }
            if let Some(slot) = by_size.get_mut(size) {
                *slot = found;
            }
        }
        Ok(by_size)
    }

    /// The largest subcomplex inside `bound`: its cells in each degree from
    /// zero to the bound's degree, with the faces of each.
    ///
    /// # Specification
    /// - ensures: a cell is in the truncation exactly when it is proper, inside
    ///   the bound, and each of its faces is in the truncation.
    /// - fails: as [`Complex::faces`] fails on a cell inside the bound.
    /// - panics: none.
    /// - executable: none — the ensures is a statement about each cell inside
    ///   the bound, which the call builds only once.
    /// - intension: the cells of a degree extend the cells of the degree below
    ///   by one arrow, so the walk builds no cell twice.
    ///
    /// # Errors
    /// - [`LawvereError`]: as the faces of a cell fail.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a theory whose rules keep their variables has a
    ///   boundary of each boundary that is zero, which a missing face breaks.
    /// - witness: `tests::lawvere::the_boundary_of_each_boundary_in_a_truncation_is_zero`
    #[inline]
    pub fn truncation(
        &mut self,
        bound: BarBound,
    ) -> Result<Truncation, LawvereError>
    {
        let mut forms: Vec<Vec<Vec<TermPlace>>> = Vec::new();
        for context in 0 ..= usize::from(bound.variables) {
            forms.push(self.normal_forms(Arity::from(context), bound.weight)?);
        }
        let point = BarCell(Vec::new());
        let mut out = Truncation {
            cells: vec![vec![point.clone()]],
            faces: BTreeMap::new(),
        };
        let _point = out.faces.insert(point.clone(), Vec::new());
        let mut previous: Vec<BarCell> = vec![point];
        let mut candidates: Vec<BarCell> = Vec::new();
        let mut faces: Vec<(BarCell, Incidence)> = Vec::new();
        for _degree in 1 ..= usize::from(bound.degree) {
            candidates.clear();
            for cell in &previous {
                let target = cell
                    .0
                    .last()
                    .map_or(Arity::from(1_usize), |last| last.source);
                let room = usize::from(bound.weight)
                    .saturating_sub(usize::from(cell.weight(&self.table)?));
                for (context, sized) in forms.iter().enumerate() {
                    for terms in tuples((sized, &self.table), target, TermSize::from(room))? {
                        let mut arrows = cell.0.clone();
                        arrows.push(Arrow {
                            source: Arity::from(context),
                            terms,
                        });
                        let candidate = BarCell(arrows);
                        if candidate.degeneracy(&self.table)? == Degeneracy::Proper {
                            candidates.push(candidate);
                        }
                    }
                }
            }
            let mut kept = Vec::new();
            while let Some(candidate) = candidates.pop() {
                faces.clear();
                self.faces(&candidate, &mut faces)?;
                if faces
                    .iter()
                    .all(|&(ref face, _)| out.faces.contains_key(face))
                {
                    let _previous = out.faces.insert(candidate.clone(), faces.clone());
                    kept.push(candidate);
                }
            }
            kept.sort();
            previous.clone_from(&kept);
            out.cells.push(kept);
        }
        Ok(out)
    }
}

/// A unit of the normal-form walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Task
{
    /// Normalise the arguments of the term, then the term.
    Enter(TermPlace),
    /// The arguments have normal forms: rewrite the term at its root.
    Leave(TermPlace),
    /// The term rewrites to `rewritten`, whose normal form is the term's.
    Await
    {
        /// The term.
        place: TermPlace,
        /// What it rewrites to.
        rewritten: TermPlace,
    },
}

/// The ways to write `total` as an ordered sum of `parts` positive sizes.
///
/// # Specification
/// trivial.
fn compositions(
    total: TermSize,
    parts: Arity,
) -> Vec<Vec<TermSize>>
{
    let parts = usize::from(parts);
    let mut out = Vec::new();
    let mut pending: Vec<(Vec<TermSize>, usize)> = vec![(Vec::new(), usize::from(total))];
    while let Some((prefix, remaining)) = pending.pop() {
        if prefix.len() == parts {
            if remaining == 0 {
                out.push(prefix);
            }
            continue;
        }
        let after = parts.saturating_sub(prefix.len()).saturating_sub(1);
        for first in 1 ..= remaining.saturating_sub(after) {
            let mut next = prefix.clone();
            next.push(TermSize::from(first));
            pending.push((next, remaining.saturating_sub(first)));
        }
    }
    out
}

/// The tuples of `length` normal forms from `sized`, listed by size in
/// `table`, whose sizes sum to at most `room`.
///
/// # Specification
/// trivial.
fn tuples(
    (sized, table): (&[Vec<TermPlace>], &TermTable),
    length: Arity,
    room: TermSize,
) -> Result<Vec<Vec<TermPlace>>, LawvereError>
{
    let room = usize::from(room);
    let mut out: Vec<(Vec<TermPlace>, usize)> = vec![(Vec::new(), 0)];
    let mut longer: Vec<(Vec<TermPlace>, usize)> = Vec::new();
    for _ in 0 .. usize::from(length) {
        longer.clear();
        for &(ref tuple, used) in &out {
            for forms in sized.iter().skip(1) {
                for &form in forms {
                    let total = used.saturating_add(usize::from(table.size(form)?));
                    if total > room {
                        continue;
                    }
                    let mut next = tuple.clone();
                    next.push(form);
                    longer.push((next, total));
                }
            }
        }
        core::mem::swap(&mut out, &mut longer);
    }
    Ok(out.into_iter().map(|(tuple, _)| tuple).collect())
}

/// A morphism of the theory: a tuple of normal forms in `source` variables.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arrow
{
    /// The variables of the context.
    pub source: Arity,
    /// The terms, one for each variable of the tuple before.
    pub terms: Vec<TermPlace>,
}

/// Whether an arrow is an identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Identity
{
    /// The arrow takes each variable of its context to itself.
    Identity,
    /// The arrow is another tuple.
    Other,
}

impl Arrow
{
    /// Whether the arrow is an identity in `table`.
    ///
    /// # Specification
    /// trivial.
    fn identity(
        &self,
        table: &TermTable,
    ) -> Result<Identity, LawvereError>
    {
        if usize::from(self.source) != self.terms.len() {
            return Ok(Identity::Other);
        }
        for (place, &term) in self.terms.iter().enumerate() {
            if table.node(term)?.head != TermHead::Var(Variable::from(place)) {
                return Ok(Identity::Other);
            }
        }
        Ok(Identity::Identity)
    }
}

/// A cell of the bar complex: a composable list of arrows, the first one
/// term.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BarCell(pub Vec<Arrow>);

/// Whether a cell counts zero.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Degeneracy
{
    /// The first term is a variable, or a later arrow is an identity.
    Degenerate,
    /// The cell is a generator.
    Proper,
}

impl BarCell
{
    /// The degree of the cell: the number of its arrows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn degree(&self) -> BarDegree
    {
        BarDegree::from(self.0.len())
    }

    /// Whether the cell is degenerate in `table`.
    ///
    /// # Specification
    /// - ensures: [`Degeneracy::Degenerate`] exactly when the first arrow holds
    ///   no term or a variable first, or a later arrow is an identity. The
    ///   empty cell is proper.
    /// - fails: [`LawvereError::Unissued`] when a term is not in the table.
    /// - panics: none.
    /// - executable: none — the ensures reads the nodes of the table, which the
    ///   predicate cannot name past the borrow.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: a term is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a leading variable, a later identity and a proper
    ///   cell separate the two classes.
    /// - witness: `tests::lawvere::a_cell_is_degenerate_on_a_leading_variable_or_a_later_identity`
    #[inline]
    pub fn degeneracy(
        &self,
        table: &TermTable,
    ) -> Result<Degeneracy, LawvereError>
    {
        let Some((first, later)) = self.0.split_first()
        else {
            return Ok(Degeneracy::Proper);
        };
        let Some(&lead) = first.terms.first()
        else {
            return Ok(Degeneracy::Degenerate);
        };
        match table.node(lead)?.head {
            TermHead::Var(_) => return Ok(Degeneracy::Degenerate),
            TermHead::Op(_) => {},
        }
        for arrow in later {
            match arrow.identity(table)? {
                Identity::Identity => return Ok(Degeneracy::Degenerate),
                Identity::Other => {},
            }
        }
        Ok(Degeneracy::Proper)
    }

    /// The total size of the cell's terms in `table`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: a term is not in the table.
    #[inline]
    pub fn weight(
        &self,
        table: &TermTable,
    ) -> Result<TermSize, LawvereError>
    {
        let mut total = 0_usize;
        for &term in self.0.iter().flat_map(|arrow| &arrow.terms) {
            total = total.saturating_add(usize::from(table.size(term)?));
        }
        Ok(TermSize::from(total))
    }
}

/// Add `coefficient` times `cell` to `chain`, a degenerate cell counting
/// zero.
///
/// # Specification
/// trivial.
fn accumulate(
    (chain, table): (&mut BTreeMap<BarCell, Incidence>, &TermTable),
    cell: BarCell,
    coefficient: Incidence,
) -> Result<(), LawvereError>
{
    if i64::from(coefficient) == 0 || cell.degeneracy(table)? == Degeneracy::Degenerate {
        return Ok(());
    }
    let entry = chain.entry(cell).or_default();
    *entry = Incidence::from(i64::from(*entry).saturating_add(i64::from(coefficient)));
    Ok(())
}

/// `(−1)ⁱ` for `i = index`.
///
/// # Specification
/// trivial.
fn sign(index: BarDegree) -> Incidence
{
    if usize::from(index) & 1 == 0 {
        Incidence::from(1_i64)
    }
    else {
        Incidence::from(-1_i64)
    }
}

/// The count of `count` as an incidence.
///
/// # Specification
/// trivial.
fn incidence(count: Occurrences) -> Result<Incidence, LawvereError>
{
    i64::try_from(usize::from(count))
        .map(Incidence::from)
        .map_err(|_overflow| LawvereError::Overflow)
}

impl Complex for LawvereTheory
{
    type Cell = BarCell;
    type Fault = LawvereError;

    /// Whether `cell` lies in the bar complex.
    ///
    /// # Specification
    /// - ensures: [`Standing::Inside`] exactly when the cell is proper, each
    ///   arrow holds one term for each variable of the arrow before, the first
    ///   arrow holds one term, and each term is a normal form in the variables
    ///   of its arrow's context.
    /// - fails: as [`LawvereTheory::normal_form`] fails.
    /// - panics: none.
    /// - executable: none — the ensures reads the normal forms, which the call
    ///   finds once.
    ///
    /// # Errors
    /// - [`LawvereError`]: as a normal form fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a degenerate cell, a cell whose arrows do not
    ///   compose, a cell with a term out of normal form and a proper cell
    ///   separate the two standings.
    /// - witness: `tests::lawvere::a_cell_outside_the_complex_stands_outside`
    #[inline]
    fn standing(
        &mut self,
        cell: &BarCell,
    ) -> Result<Standing, LawvereError>
    {
        if cell.degeneracy(&self.table)? == Degeneracy::Degenerate {
            return Ok(Standing::Outside);
        }
        let mut width = 1_usize;
        let mut counts = BTreeMap::new();
        for arrow in &cell.0 {
            if arrow.terms.len() != width {
                return Ok(Standing::Outside);
            }
            for &term in &arrow.terms {
                if self.normal_form(term)? != term {
                    return Ok(Standing::Outside);
                }
                self.table.occurrences(term, &mut counts)?;
                if counts
                    .keys()
                    .any(|&variable| variable >= Variable::from(usize::from(arrow.source)))
                {
                    return Ok(Standing::Outside);
                }
            }
            width = usize::from(arrow.source);
        }
        Ok(Standing::Inside)
    }

    /// Push each face of `cell` onto `faces`, with its incidence: the first
    /// face, each inner face and the last face, equal faces summed.
    ///
    /// # Specification
    /// - requires: `cell` lies in the complex.
    /// - ensures: each face with a nonzero sum is pushed once, in cell order,
    ///   after the entries that `faces` held before. No degenerate face is
    ///   pushed.
    /// - fails: [`LawvereError::NoTerm`] when the first arrow holds no term;
    ///   [`LawvereError::Unfilled`] when an arrow does not fill a variable of
    ///   the arrow before; [`LawvereError::Overflow`] when a coefficient passes
    ///   an incidence; and as [`LawvereTheory::normal_form`] fails.
    /// - panics: none.
    /// - executable: none — the ensures sums the faces, and the call holds no
    ///   second sum to check it against.
    /// - intension: each inner face takes one composite in normal form, and the
    ///   faces are summed in one ordered map.
    ///
    /// # Errors
    /// - [`LawvereError`]: as named under `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cell whose first and last faces are equal sums
    ///   them, and a cell whose inner composite rewrites cancels its first face
    ///   against it.
    /// - witness: `tests::lawvere::the_faces_of_a_cell_are_its_first_inner_and_last_faces`
    /// - witness: `tests::lawvere::the_boundary_of_each_boundary_in_a_truncation_is_zero`
    #[inline]
    fn faces(
        &mut self,
        cell: &BarCell,
        faces: &mut Vec<(BarCell, Incidence)>,
    ) -> Result<(), LawvereError>
    {
        let arrows = &cell.0;
        let Some(first) = arrows.first()
        else {
            return Ok(());
        };
        let lead = *first.terms.first().ok_or(LawvereError::NoTerm)?;
        let mut occurrences = BTreeMap::new();
        self.table.occurrences(lead, &mut occurrences)?;
        let mut chain: BTreeMap<BarCell, Incidence> = BTreeMap::new();
        let degree = arrows.len();
        let mut second = arrows.iter().skip(1);
        match second.next() {
            None => {
                let total = occurrences
                    .values()
                    .map(|&count| usize::from(count))
                    .fold(0, usize::saturating_add);
                let total = i64::from(incidence(Occurrences::from(total))?);
                accumulate(
                    (&mut chain, &self.table),
                    BarCell(Vec::new()),
                    Incidence::from(total.saturating_sub(1)),
                )?;
            },
            Some(second) => {
                for (&variable, &count) in &occurrences {
                    let term = *second
                        .terms
                        .get(usize::from(variable))
                        .ok_or(LawvereError::Unfilled(variable))?;
                    let mut face = vec![Arrow {
                        source: second.source,
                        terms: vec![term],
                    }];
                    face.extend(arrows.iter().skip(2).cloned());
                    accumulate((&mut chain, &self.table), BarCell(face), incidence(count)?)?;
                }
                for (inner, (outer, filler)) in arrows.iter().zip(arrows.iter().skip(1)).enumerate()
                {
                    let mut terms = Vec::with_capacity(outer.terms.len());
                    for &term in &outer.terms {
                        let composite = self.table.substituted(term, &filler.terms)?;
                        terms.push(self.normal_form(composite)?);
                    }
                    let mut face: Vec<Arrow> = arrows.iter().take(inner).cloned().collect();
                    face.push(Arrow {
                        source: filler.source,
                        terms,
                    });
                    face.extend(arrows.iter().skip(inner.saturating_add(2)).cloned());
                    accumulate(
                        (&mut chain, &self.table),
                        BarCell(face),
                        sign(BarDegree::from(inner.saturating_add(1))),
                    )?;
                }
                let last = BarCell(
                    arrows
                        .iter()
                        .take(degree.saturating_sub(1))
                        .cloned()
                        .collect(),
                );
                accumulate(
                    (&mut chain, &self.table),
                    last,
                    sign(BarDegree::from(degree)),
                )?;
            },
        }
        faces.extend(
            chain
                .into_iter()
                .filter(|&(_, coefficient)| i64::from(coefficient) != 0),
        );
        Ok(())
    }
}

/// The bound of a truncation: the variables of each arrow's context, the
/// total size of a cell's terms, and the highest degree.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BarBound
{
    /// The most variables in a context.
    pub variables: Arity,
    /// The largest total size of a cell's terms.
    pub weight: TermSize,
    /// The highest degree of a cell.
    pub degree: BarDegree,
}

quenchant_shape::reason_enum! {
    /// Why a truncation lists no faces for a cell.
    pub mod truncated {
        /// The reason the cell has no entry.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The cell is not in the truncation.
            Outside,
        }
    }
}

/// The cells of the largest subcomplex inside a bound, by degree, with the
/// faces of each.
#[derive(Clone, Debug, Default)]
pub struct Truncation
{
    /// The cells of each degree, in cell order.
    cells: Vec<Vec<BarCell>>,
    /// The faces of each cell.
    faces: BTreeMap<BarCell, Vec<(BarCell, Incidence)>>,
}

impl Truncation
{
    /// The cells of `degree`, in cell order, and none past the bound's
    /// degree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(
        &self,
        degree: BarDegree,
    ) -> &[BarCell]
    {
        self.cells
            .get(usize::from(degree))
            .map_or(&[][..], Vec::as_slice)
    }

    /// The faces of `cell`, with their incidences.
    ///
    /// # Specification
    /// - provides: [`truncated::Absent::Outside`] when the cell is not in the
    ///   truncation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each face of a kept cell has an entry, and a cell
    ///   past the bound has none.
    /// - witness: `tests::lawvere::the_boundary_of_each_boundary_in_a_truncation_is_zero`
    #[inline]
    #[must_use]
    pub fn faces(
        &self,
        cell: &BarCell,
    ) -> Maybe<&[(BarCell, Incidence)], truncated::Absent>
    {
        self.faces
            .get(cell)
            .map_or(Maybe::Absent(truncated::Absent::Outside), |faces| {
                Maybe::Present(faces.as_slice())
            })
    }
}
