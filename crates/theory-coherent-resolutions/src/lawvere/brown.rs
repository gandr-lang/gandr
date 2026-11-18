//! Brown's collapsing scheme on the bar complex of a Lawvere theory.
//!
//! A collapsing scheme matches the cells of the bar complex in pairs. Each pair
//! holds a redundant cell and a collapsible cell one degree above it. The
//! redundant cell is a face of its partner with the incidence one or minus
//! one. The cells that stay unmatched are essential. When the matching has no
//! cycle, the complex contracts onto a complex of its essential cells.
//!
//! The scheme follows the normalisation strategy along the reduction order:
//! the leftmost innermost redex, and the rules in their order at one node. It
//! reads a cell `[u₁|…|uₙ]` from the left. The composite `u₁ ∘ … ∘ uⱼ` marks
//! each node with the arrow it comes from. Step `j` takes the first redex of
//! that composite that reads a node of `uⱼ₋₁` or of `uⱼ`.
//!
//! | Step | Case | Class | Partner |
//! | --- | --- | --- | --- |
//! | first | `u₁ = f(t₁, …, tₐ)` is no generator `f(x₁, …, xₐ)` | redundant | `[f(x₁, …, xₐ)\|(t₁, …, tₐ)\|u₂\|…\|uₙ]` |
//! | `j` | no redex, or the redex reads no node of `uⱼ` | collapsible | the cell with `uⱼ₋₁ ∘ uⱼ` for the two arrows |
//! | `j` | the redex reads `uⱼ = y ∘ z` through its top `y`, and `z` is no identity | redundant | the cell with `y\|z` for `uⱼ` |
//! | `j` | the redex reads all of `uⱼ` | the next step | |
//! | after `n` | each step reads all of its arrow | essential | none |
//!
//! The top `y` keeps the nodes of `uⱼ` that the redex reads. A fresh variable
//! stands for each subterm below them, in pre-order. The tuple `z` holds those
//! subterms.
//!
//! An essential cell of degree one is a generator. One of degree two is a
//! rule's left side `[f(x₁, …, xₐ)|y]`. One of degree three is an overlap of
//! two rules, and [`LawvereTheory::overlapping`] names its second rule.
//!
//! # References
//!
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-frame-squier — completion is a Morse collapse of a
//!   resolution, and this scheme is that collapse.
//! - `Guiraud-2019-convergent_presentations_polygraphic_resolutions_associative_algebras`
//!   — exemplar: collapsing schemes that contract the standard resolution onto
//!   the rules and the critical branchings, after Brown.
//! - Kenneth S. Brown. "The Geometry of Rewriting Systems: A Proof of the
//!   Anick–Groves–Squier Theorem." In _Algorithms and Classification in
//!   Combinatorial Group Theory_, MSRI Publications 23, 1992, pages 137–163 —
//!   the collapsing scheme of the bar complex along a rewriting strategy.
//! - `Malbos-2021-completion_operads_essential_syzygies` — background: § 2
//!   calls a critical branching essential when its two rewriting monomials are
//!   consecutive. Theorem 3.3 decides confluence on the essential branchings
//!   alone. This scheme keeps each critical branching essential, so its
//!   collapse removes no branching that completion joins.
//! - `Doré-2023-computing_spaces_type_theory` — background: § 3.4 states a
//!   matching as a function whose fixed points are the critical cells. The
//!   class of a cell is that function here. § 3.4 states acyclicity as a
//!   gradient path from each cell to a critical cell. The Morse crate checks
//!   only that the gradient from the given cells holds no cycle.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::Range;

use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Scheme;
use quenchant_shape::shape::Maybe;

use super::Agreement;
use super::Arrow;
use super::BarCell;
use super::Identity;
use super::LawvereError;
use super::LawvereTheory;
use super::TermHead;
use super::TermNode;
use super::TermTable;
use super::identity;
use crate::boundary::Arity;
use crate::boundary::Operation;
use crate::boundary::RulePlace;
use crate::boundary::TermPlace;
use crate::boundary::Variable;

/// The arrow of a cell that a node of a composite comes from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Level(usize);

/// A node's place in a composite. Each node comes after its arguments.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Place(usize);

/// Where a node of an arrow lies: the arrow's term, and the node's place in
/// the pre-order of that term.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Origin
{
    /// The term of the arrow.
    term: usize,
    /// The node's place in the term's pre-order.
    node: usize,
}

/// One node of a composite.
#[derive(Clone, Debug)]
struct Spot
{
    /// The symbol.
    head: TermHead,
    /// The arrow the node comes from.
    level: Level,
    /// Where the node lies in the last arrow of the composite. A node of an
    /// arrow before the last keeps the default.
    origin: Origin,
    /// The arguments, a range of [`Memory::arguments`].
    arguments: Range<usize>,
}

/// Whether a node starts a term of its arrow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fresh
{
    /// The node is the root of its term.
    Root,
    /// The node lies below the root.
    Inner,
}

/// One step of the walk that builds a composite.
#[derive(Clone, Copy, Debug)]
enum Build
{
    /// Read the node at `term` of the arrow at `level`, in that arrow's term
    /// `of`.
    Enter
    {
        /// The node.
        term: TermPlace,
        /// Its arrow.
        level: Level,
        /// The term of the arrow it lies in.
        of: usize,
        /// Whether it is the root of that term.
        fresh: Fresh,
    },
    /// Make a node from the last `arity` nodes built.
    Leave
    {
        /// The symbol.
        head: TermHead,
        /// Its arrow.
        level: Level,
        /// Where it lies in its arrow.
        origin: Origin,
        /// The number of its arguments.
        arity: usize,
    },
}

/// One step of the walk that reads an arrow below the nodes a redex keeps.
#[derive(Clone, Copy, Debug)]
enum Cut
{
    /// Read the node at the term, which lies at the given place in the
    /// pre-order of its term.
    Enter(TermPlace, usize),
    /// Make the operation from the last terms built, as many as the count.
    Leave(Operation, usize),
}

/// Whether a redex of a composite reads a node of the given arrows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Redex
{
    /// The first such redex, by its rule.
    Found(RulePlace),
    /// No redex reads a node of the arrows.
    Missing,
}

quenchant_shape::reason_enum! {
    /// Why a cell names no overlapping rule.
    pub mod overlapped {
        /// The reason no rule is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The cell has fewer than two arrows.
            Short,
            /// No redex of the composite reads a node of the cell's last two
            /// arrows.
            NoRedex,
        }
    }
}

/// The working memory of the scheme, kept from one cell to the next.
#[derive(Clone, Debug)]
pub(super) struct Memory
{
    /// The nodes of the composite, each after its arguments.
    spots: Vec<Spot>,
    /// The arguments of every node of the composite, in order.
    arguments: Vec<Place>,
    /// The steps that the walk which builds the composite has still to take.
    building: Vec<Build>,
    /// The nodes built that no node above holds yet.
    built: Vec<Place>,
    /// The pairs of pattern and node that a match has still to read.
    matching: Vec<(TermPlace, Place)>,
    /// The nodes that the last match reads.
    region: Vec<Place>,
    /// The nodes of the last arrow that the selected redex reads, in order.
    kept: Vec<Origin>,
    /// The steps that the walk which reads or splits an arrow has still to
    /// take.
    cutting: Vec<Cut>,
    /// The arguments of one node, each with its place in the pre-order.
    children: Vec<(TermPlace, usize)>,
    /// The terms that a split builds and that no term above holds yet.
    pieces: Vec<TermPlace>,
}

impl Memory
{
    /// Working memory that holds nothing.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn new() -> Self
    {
        Self {
            spots: Vec::new(),
            arguments: Vec::new(),
            building: Vec::new(),
            built: Vec::new(),
            matching: Vec::new(),
            region: Vec::new(),
            kept: Vec::new(),
            cutting: Vec::new(),
            children: Vec::new(),
            pieces: Vec::new(),
        }
    }

    /// Build the composite of `arrows` up to the arrow at `last`, each node
    /// marked with its arrow.
    ///
    /// # Specification
    /// trivial.
    fn build(
        &mut self,
        table: &TermTable,
        (arrows, last): (&[Arrow], Level),
    ) -> Result<(), LawvereError>
    {
        self.spots.clear();
        self.arguments.clear();
        self.built.clear();
        self.building.clear();
        let root = arrows
            .first()
            .and_then(|arrow| arrow.terms.first())
            .copied()
            .ok_or(LawvereError::NoTerm)?;
        self.building.push(Build::Enter {
            term: root,
            level: Level(0),
            of: 0,
            fresh: Fresh::Root,
        });
        let mut counter = 0_usize;
        while let Some(step) = self.building.pop() {
            match step {
                Build::Enter {
                    term,
                    level,
                    of,
                    fresh,
                } => {
                    let node = table.node(term)?;
                    match node.head {
                        TermHead::Var(variable) if level < last => {
                            let next = Level(level.0.saturating_add(1));
                            let place = usize::from(variable);
                            let term = arrows
                                .get(next.0)
                                .and_then(|arrow| arrow.terms.get(place))
                                .copied()
                                .ok_or(LawvereError::Unfilled(variable))?;
                            self.building.push(Build::Enter {
                                term,
                                level: next,
                                of: place,
                                fresh: Fresh::Root,
                            });
                        },
                        head @ (TermHead::Var(_) | TermHead::Op(_)) => {
                            let origin = if level == last {
                                if fresh == Fresh::Root {
                                    counter = 0;
                                }
                                let origin = Origin {
                                    term: of,
                                    node: counter,
                                };
                                counter = counter.saturating_add(1);
                                origin
                            }
                            else {
                                Origin::default()
                            };
                            self.building.push(Build::Leave {
                                head,
                                level,
                                origin,
                                arity: node.children.len(),
                            });
                            self.building
                                .extend(node.children.iter().rev().map(|&child| Build::Enter {
                                    term: child,
                                    level,
                                    of,
                                    fresh: Fresh::Inner,
                                }));
                        },
                    }
                },
                Build::Leave {
                    head,
                    level,
                    origin,
                    arity,
                } => {
                    let start = self.built.len().saturating_sub(arity);
                    let from = self.arguments.len();
                    self.arguments.extend(self.built.drain(start ..));
                    self.built.push(Place(self.spots.len()));
                    self.spots.push(Spot {
                        head,
                        level,
                        origin,
                        arguments: from .. self.arguments.len(),
                    });
                },
            }
        }
        Ok(())
    }

    /// Whether the left side `pattern` matches the composite at `place`. The
    /// nodes that it reads stay in `self.region`. Each left side is linear, so
    /// a variable of the pattern matches any node.
    ///
    /// # Specification
    /// trivial.
    fn matched(
        &mut self,
        table: &TermTable,
        (pattern, place): (TermPlace, Place),
    ) -> Result<Agreement, LawvereError>
    {
        self.matching.clear();
        self.region.clear();
        self.matching.push((pattern, place));
        while let Some((pattern, place)) = self.matching.pop() {
            let want = table.node(pattern)?;
            if let TermHead::Var(_) = want.head {
                continue;
            }
            let Some(have) = self.spots.get(place.0)
            else {
                return Ok(Agreement::Differs);
            };
            let Some(arguments) = self.arguments.get(have.arguments.clone())
            else {
                return Ok(Agreement::Differs);
            };
            if have.head != want.head || arguments.len() != want.children.len() {
                return Ok(Agreement::Differs);
            }
            self.region.push(place);
            self.matching
                .extend(want.children.iter().copied().zip(arguments.iter().copied()));
        }
        Ok(Agreement::Agrees)
    }

    /// The first redex of the composite that reads a node of `levels`, nodes
    /// in post-order and rules in order at each node. Its nodes stay in
    /// `self.region`.
    ///
    /// # Specification
    /// trivial.
    fn first_redex(
        &mut self,
        (rules, table): (&[(TermPlace, TermPlace)], &TermTable),
        levels: (Level, Level),
    ) -> Result<Redex, LawvereError>
    {
        for place in 0 .. self.spots.len() {
            for (rule, &(left, _)) in rules.iter().enumerate() {
                if self.matched(table, (left, Place(place)))? == Agreement::Differs {
                    continue;
                }
                let spots = &self.spots;
                let reads = self.region.iter().any(|read| {
                    spots
                        .get(read.0)
                        .is_some_and(|spot| spot.level == levels.0 || spot.level == levels.1)
                });
                if reads {
                    return Ok(Redex::Found(RulePlace::from(rule)));
                }
            }
        }
        Ok(Redex::Missing)
    }

    /// Push the arguments of `held`, the node at `origin`, each with its own
    /// place in the pre-order of its term.
    ///
    /// # Specification
    /// trivial.
    fn descend(
        &mut self,
        table: &TermTable,
        (held, origin): (&TermNode, Origin),
    ) -> Result<(), LawvereError>
    {
        let mut next = origin.node.saturating_add(1);
        self.children.clear();
        for &child in &held.children {
            self.children.push((child, next));
            next = next.saturating_add(usize::from(table.size(child)?));
        }
        while let Some((child, at)) = self.children.pop() {
            self.cutting.push(Cut::Enter(child, at));
        }
        Ok(())
    }

    /// Whether the tuple below the nodes of `arrow` that `self.kept` names is
    /// an identity: each subterm below them, in pre-order, is the next
    /// variable, and they are as many as the variables of the context.
    ///
    /// # Specification
    /// trivial.
    fn whole(
        &mut self,
        table: &TermTable,
        arrow: &Arrow,
    ) -> Result<Identity, LawvereError>
    {
        let mut fresh = 0_usize;
        for (of, &root) in arrow.terms.iter().enumerate() {
            self.cutting.clear();
            self.cutting.push(Cut::Enter(root, 0));
            while let Some(step) = self.cutting.pop() {
                match step {
                    Cut::Enter(term, node) => {
                        let held = table.node(term)?;
                        match held.head {
                            TermHead::Op(_)
                                if self.kept.binary_search(&Origin { term: of, node }).is_ok() =>
                            {
                                self.descend(table, (held, Origin { term: of, node }))?;
                            },
                            TermHead::Var(variable) if usize::from(variable) == fresh => {
                                fresh = fresh.saturating_add(1);
                            },
                            TermHead::Op(_) | TermHead::Var(_) => return Ok(Identity::Other),
                        }
                    },
                    Cut::Leave(..) => {},
                }
            }
        }
        if fresh == usize::from(arrow.source) {
            Ok(Identity::Identity)
        }
        else {
            Ok(Identity::Other)
        }
    }

    /// `arrow` split as `top ∘ rest`. The top keeps each node that
    /// `self.kept` names. A fresh variable stands for each subterm below them,
    /// in pre-order, and `rest` holds those subterms.
    ///
    /// # Specification
    /// trivial.
    fn split(
        &mut self,
        table: &mut TermTable,
        arrow: &Arrow,
    ) -> Result<(Arrow, Arrow), LawvereError>
    {
        let mut fresh: Vec<TermPlace> = Vec::new();
        let mut tops = Vec::with_capacity(arrow.terms.len());
        for (of, &root) in arrow.terms.iter().enumerate() {
            self.cutting.clear();
            self.pieces.clear();
            self.cutting.push(Cut::Enter(root, 0));
            while let Some(step) = self.cutting.pop() {
                match step {
                    Cut::Enter(term, node) => {
                        let held = table.node(term)?;
                        match held.head {
                            TermHead::Op(operation)
                                if self.kept.binary_search(&Origin { term: of, node }).is_ok() =>
                            {
                                self.cutting
                                    .push(Cut::Leave(operation, held.children.len()));
                                self.descend(table, (held, Origin { term: of, node }))?;
                            },
                            TermHead::Op(_) | TermHead::Var(_) => {
                                let variable = Variable::from(fresh.len());
                                fresh.push(term);
                                self.pieces.push(table.var(variable));
                            },
                        }
                    },
                    Cut::Leave(operation, arity) => {
                        let start = self.pieces.len().saturating_sub(arity);
                        let arguments = self.pieces.split_off(start);
                        self.pieces.push(table.op(operation, arguments)?);
                    },
                }
            }
            tops.push(self.pieces.pop().ok_or(LawvereError::Unissued(root))?);
        }
        Ok((
            Arrow {
                source: Arity::from(fresh.len()),
                terms: tops,
            },
            Arrow {
                source: arrow.source,
                terms: fresh,
            },
        ))
    }

    /// The class of `cell` under the scheme of the theory of `rules` over
    /// `table`.
    ///
    /// # Specification
    /// trivial.
    fn class(
        &mut self,
        (rules, table): (&[(TermPlace, TermPlace)], &mut TermTable),
        cell: &BarCell,
    ) -> Result<Class<BarCell>, LawvereError>
    {
        let arrows = cell.0.as_slice();
        let Some(first) = arrows.first()
        else {
            return Ok(Class::Critical);
        };
        let lead = first.terms.first().copied().ok_or(LawvereError::NoTerm)?;
        let node = table.node(lead)?;
        let TermHead::Op(operation) = node.head
        else {
            return Err(LawvereError::LeadingVariable);
        };
        if first.terms.len() != 1
            || identity(table, (first.source, &node.children))? == Identity::Other
        {
            let children = node.children.clone();
            let mut split = Vec::with_capacity(arrows.len().saturating_add(1));
            split.push(table.generator(operation, Arity::from(children.len()))?);
            split.push(Arrow {
                source: first.source,
                terms: children,
            });
            split.extend(arrows.iter().skip(1).cloned());
            return Ok(Class::Redundant(BarCell(split)));
        }
        for (before, (outer, filler)) in arrows.iter().zip(arrows.iter().skip(1)).enumerate() {
            let at = before.saturating_add(1);
            let level = Level(at);
            self.build(table, (arrows, level))?;
            self.kept.clear();
            match self.first_redex((rules, table), (Level(before), level))? {
                Redex::Found(_) => {
                    let spots = &self.spots;
                    self.kept.extend(
                        self.region
                            .iter()
                            .filter_map(|read| spots.get(read.0))
                            .filter(|spot| spot.level == level)
                            .map(|spot| spot.origin),
                    );
                    self.kept.sort_unstable();
                    self.kept.dedup();
                },
                Redex::Missing => {},
            }
            if self.kept.is_empty() {
                let mut terms = Vec::with_capacity(outer.terms.len());
                for &held in &outer.terms {
                    terms.push(table.substituted(held, &filler.terms)?);
                }
                let mut merged = Vec::with_capacity(arrows.len().saturating_sub(1));
                merged.extend(arrows.iter().take(before).cloned());
                merged.push(Arrow {
                    source: filler.source,
                    terms,
                });
                merged.extend(arrows.iter().skip(at.saturating_add(1)).cloned());
                return Ok(Class::Collapsible(BarCell(merged)));
            }
            if self.whole(table, filler)? == Identity::Identity {
                continue;
            }
            let (top, rest) = self.split(table, filler)?;
            let mut parted = Vec::with_capacity(arrows.len().saturating_add(1));
            parted.extend(arrows.iter().take(at).cloned());
            parted.push(top);
            parted.push(rest);
            parted.extend(arrows.iter().skip(at.saturating_add(1)).cloned());
            return Ok(Class::Redundant(BarCell(parted)));
        }
        Ok(Class::Critical)
    }
}

impl TermTable
{
    /// The generator `f(x₁, …, xₐ)` of `operation` of arity `arity`: the
    /// arrow from `arity` variables to the one term.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`LawvereError::Unissued`]: as [`TermTable::op`] fails.
    #[inline]
    pub fn generator(
        &mut self,
        operation: Operation,
        arity: Arity,
    ) -> Result<Arrow, LawvereError>
    {
        let mut children = Vec::with_capacity(usize::from(arity));
        for place in 0 .. usize::from(arity) {
            children.push(self.var(Variable::from(place)));
        }
        Ok(Arrow {
            source: arity,
            terms: vec![self.op(operation, children)?],
        })
    }
}

impl LawvereTheory
{
    /// The rule of the first redex, along the scheme's order, of the
    /// composite of `cell` that reads a node of its last two arrows. For an
    /// essential cell of degree three, that rule's left side overlaps the
    /// left side that the first two arrows spell.
    ///
    /// # Specification
    /// - requires: each arrow of `cell` holds one term for each variable of the
    ///   arrow before it, and each rule's left side is linear.
    /// - provides: [`overlapped::Absent::Short`] for a cell of fewer than two
    ///   arrows, and [`overlapped::Absent::NoRedex`] when no redex of the
    ///   composite reads a node of the last two arrows.
    /// - fails: [`LawvereError::NoTerm`] when the first arrow holds no term;
    ///   [`LawvereError::Unfilled`] when an arrow holds no term for a variable
    ///   of the arrow before it; [`LawvereError::Unissued`] when a place is not
    ///   in the table.
    /// - panics: none.
    /// - executable: none — the ensures reads the composite of the cell's
    ///   arrows, which the call builds once.
    ///
    /// # Errors
    /// - [`LawvereError::NoTerm`]: the first arrow holds no term.
    /// - [`LawvereError::Unfilled`]: an arrow holds no term for a variable.
    /// - [`LawvereError::Unissued`]: a place is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two overlaps of `NatUnits` name their two rules,
    ///   and a cell of one arrow and a cell with no redex name none.
    /// - witness: `tests::brown::an_overlap_names_the_rule_that_it_overlaps`
    #[inline]
    pub fn overlapping(
        &mut self,
        cell: &BarCell,
    ) -> Result<Maybe<RulePlace, overlapped::Absent>, LawvereError>
    {
        let &mut Self {
            ref rules,
            ref mut table,
            ref mut scheme,
            ..
        } = self;
        let Some(last) = cell.0.len().checked_sub(1).filter(|&last| last > 0)
        else {
            return Ok(Maybe::Absent(overlapped::Absent::Short));
        };
        scheme.build(table, (&cell.0, Level(last)))?;
        match scheme.first_redex(
            (rules.as_slice(), table),
            (Level(last.saturating_sub(1)), Level(last)),
        )? {
            Redex::Found(rule) => Ok(Maybe::Present(rule)),
            Redex::Missing => Ok(Maybe::Absent(overlapped::Absent::NoRedex)),
        }
    }
}

impl Scheme for LawvereTheory
{
    /// The class of `cell` under Brown's collapsing scheme.
    ///
    /// # Specification
    /// - requires: `cell` lies in the complex, and each rule's left side is an
    ///   operation in which each variable occurs once.
    /// - ensures: the empty cell is critical. Each other cell takes the class
    ///   of the first step in the module's table whose case holds, with that
    ///   step's partner.
    /// - fails: [`LawvereError::NoTerm`] when the first arrow holds no term;
    ///   [`LawvereError::LeadingVariable`] when it holds a variable first;
    ///   [`LawvereError::Unfilled`] when an arrow holds no term for a variable
    ///   of the arrow before it; [`LawvereError::Unissued`] when a place is not
    ///   in the table.
    /// - panics: none.
    /// - executable: none — the ensures reads the composite of the cell's
    ///   arrows, which the call builds once for each step.
    /// - intension: the theory keeps the composite in its working memory, so a
    ///   class allocates only to build its partner.
    ///
    /// # Errors
    /// - [`LawvereError::NoTerm`]: the first arrow holds no term.
    /// - [`LawvereError::LeadingVariable`]: the first arrow holds a variable.
    /// - [`LawvereError::Unfilled`]: an arrow holds no term for a variable.
    /// - [`LawvereError::Unissued`]: a place is not in the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — seven cells of `NatUnits` take each class through
    ///   each step of the table, and a cell led by a variable or by no term is
    ///   refused.
    /// - witness: `tests::brown::the_cells_of_nat_units_take_the_classes_of_the_scheme`
    /// - witness: `tests::brown::a_cell_led_by_a_variable_or_by_no_term_is_refused`
    #[inline]
    fn class(
        &mut self,
        cell: &BarCell,
    ) -> Result<Class<BarCell>, LawvereError>
    {
        let &mut Self {
            ref rules,
            ref mut table,
            ref mut scheme,
            ..
        } = self;
        scheme.class((rules.as_slice(), table), cell)
    }
}
