//! `derive r : l <=> r in T`: an equation over the operations of the theory
//! `T` that every model of `T` keeps.
//!
//! The statement holds because the theory's completed rules rewrite both
//! sides to one normal form.
//!
//! The coherence check ([`crate::coincide`]) leaves a theory's presented
//! reading a terminating, confluent store: each written law a cell, oriented as
//! the path order chose, then each rule completion derived, with the
//! certificate that the cells before it join its peak. The rewriting is the
//! proof. A step fires a cell at a position: in a model, the cell's law — or
//! its inverse, where the cell runs against the law's written direction —
//! applied to the terms the cell's left side matched, carried to the whole term
//! by the context around the position. A derived cell's law is proved from its
//! certificate: back along the path that reaches its left side from the peak,
//! then along the path that reaches its right side. [`plan`] reads that proof
//! into one [`Lemma`] per derived cell it fires, in the order completion
//! derived them, then the statement's own, which the lowering mints.
//!
//! # Boundaries
//!
//! The theory's sorts are unindexed and it nests no model, so no operation
//! binds an implicit argument and every term is read as written. A certificate
//! whose peak names a variable neither side of its rule keeps reads it as a
//! variable of the rule of its sort, or as a constant of its sort; a theory
//! with neither is refused by name.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_computads::TermAlphabet;
use gandr_theory_computads::TermProv;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use crate::coincide::Coincidence;
use crate::desc_cells::DeclarationCells;
use crate::form::Placed;
use crate::model::Binder;
use crate::model::Members;
use crate::model::ModelFault;
use crate::model::ModelForm;
use crate::model::Presentation;
use crate::model::PresentedLaw;
use crate::model::derive_laws;
use crate::model::derive_members;

/// The variable a step's context holds where its redex stood: no written
/// variable is spelled so, since a written variable is an identifier.
pub const HOLE: &str = "#";

/// The most steps one side rewrites by before [`plan`] gives up on it.
const STEPS: usize = 4096;

/// Why a statement is no rule its theory derives.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each reason is distinct and names no source position; the refusal
///   carrying it names the rule and the theory.
/// - executable: none — a fault is data a refusal carries.
///
/// # Adequacy
/// - hypothesis: L3 — two sides apart, a theory whose rules part and a side
///   naming no operation each keep their own fault.
/// - witness: `derive::tests::sides_the_completion_keeps_apart_are_refused`
/// - witness: `derive::tests::a_side_naming_no_operation_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DeriveFault
{
    /// The theory's completed rules rewrite the two sides to different normal
    /// forms.
    Apart,
    /// The theory's rules stand as no terminating, confluent system: the
    /// coherence check refused them or did not examine them, or a step of a
    /// proof fires a rule that states no law.
    Incoherent,
    /// The theory states an indexed sort or a nested model, whose terms the
    /// derivation does not read yet.
    Indexed,
    /// The theory states a component its models cannot: the fault it keeps.
    Unstated(ModelFault),
    /// A side states no law of the theory: the fault the law's derivation
    /// keeps.
    Unsorted(ModelFault),
    /// A certificate's peak names a variable neither side of its rule keeps,
    /// and the theory has no term of its sort to stand for it.
    Erased,
    /// A side rewrites past the step budget.
    Undecided,
}

impl fmt::Display for DeriveFault
{
    /// The reason, as a clause.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every fault renders a clause no other fault renders.
    /// - witness: `derive::tests::each_derive_fault_reads_as_its_own_clause`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Apart => f.write_str("its rules rewrite the two sides to different normal forms"),
            Self::Incoherent => f.write_str("its rules stand as no terminating, confluent system"),
            Self::Indexed => f.write_str(
                "it states an indexed sort or a nested model, which a rule does not read yet",
            ),
            Self::Unstated(fault) => write!(f, "it states a component that {fault}"),
            Self::Unsorted(fault) => write!(f, "the rule {fault}"),
            Self::Erased => f.write_str(
                "a certificate reads a variable of a sort no rule variable or constant inhabits",
            ),
            Self::Undecided => f.write_str("a side rewrites past the step budget"),
        }
    }
}

/// What a step fires: a law of the theory, along its written direction or
/// against it, or a lemma of the plan.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Fired
{
    /// The law the theory names so; `backward` when the cell runs from the
    /// law's right side to its left.
    Law
    {
        /// The law's name.
        name: Name,
        /// Whether the cell runs against the law.
        backward: bool,
    },
    /// The lemma at this place of the plan, earlier than the one firing it.
    Lemma(LemmaIndex),
}

/// A lemma's place in a [`plan`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LemmaIndex(pub usize);

/// One rewrite of a proof: a cell fired at one position of a term.
///
/// # Specification
/// - requires: nothing to construct this data; [`plan`] produces it.
/// - ensures: the term before the step is `context` with [`HOLE`] replaced by
///   the redex's first side, the term after with its second; the redex's sides
///   are the fired cell's sides under `substitution`.
/// - executable: none — a step is data the lowering mints.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Step
{
    /// What the step fires.
    pub fired: Fired,
    /// The term before the step, [`HOLE`] where the redex stands.
    pub context: FreeTerm,
    /// The redex, and what it rewrites to.
    pub redex: (FreeTerm, FreeTerm),
    /// The whole term before the step, and after it.
    pub whole: (FreeTerm, FreeTerm),
    /// The term each variable of the fired cell matched.
    pub substitution: BTreeMap<Name, FreeTerm>,
    /// The sort of the redex, then of the whole term.
    pub sorts: (Name, Name),
}

/// A run of steps from a term: its path, or the path back.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Leg
{
    /// The term the run starts from.
    pub from: FreeTerm,
    /// The steps, in order.
    pub steps: Vec<Step>,
    /// Whether the leg is read back, from the run's end to its start.
    pub back: bool,
}

/// A rule [`plan`] states and proves: its law, and the two legs whose
/// composite is the law's path.
///
/// # Specification
/// - requires: nothing to construct this data; [`plan`] produces it.
/// - ensures: the law is a [`ModelForm::Law`]; the first leg starts where the
///   law's left side does, read forward or back, the second ends at its right
///   side, and the two meet.
/// - executable: none — a lemma is data the lowering mints.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lemma
{
    /// The law the lemma states.
    pub law: ModelForm,
    /// The first leg, then the second.
    pub legs: [Leg; 2],
}

/// One node of a [`Flat`] term: a variable, or an operation over its argument
/// count.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Node
{
    /// A variable.
    Var(Name),
    /// An operation's application over this many arguments.
    Op(Name, Arity),
}

/// An application's argument count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Arity(usize);

/// A node's place in a [`Flat`] term's table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Place(usize);

/// A first-order term over a theory's operations, its nodes in prefix order:
/// a variable is a constant of the term, matched only by a cell's variable.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Flat(Vec<Node>);

/// Where each variable of a cell's side matched: the bounds of its image in
/// the term matched.
type Matched = BTreeMap<Name, (Place, Place)>;

impl Flat
{
    /// The term `term` spells.
    ///
    /// # Specification
    /// - ensures: one node per node of `term`, in prefix order.
    /// - fails: none for a term holding a constructor, a results tuple, an
    ///   instantiation or an abstraction.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|flat| flat.free() == *term))]
    fn of(term: &FreeTerm) -> Option<Self>
    {
        let mut nodes = Vec::new();
        let mut pending: Vec<TermNode<'_>> = vec![term.to_node()];
        while let Some(node) = pending.pop() {
            match node.view() {
                TermView::Var(name) => nodes.push(Node::Var(name.clone())),
                TermView::Op { name, args } => {
                    nodes.push(Node::Op(name.clone(), Arity(args.len())));
                    let mark = pending.len();
                    pending.extend(args);
                    if let Some(children) = pending.get_mut(mark ..) {
                        children.reverse();
                    }
                },
                TermView::Ctor { .. }
                | TermView::Results { .. }
                | TermView::Inst { .. }
                | TermView::Abs { .. } => return None,
            }
        }
        Some(Self(nodes))
    }

    /// The free term this term spells.
    ///
    /// # Specification
    /// trivial.
    fn free(&self) -> FreeTerm
    {
        let mut built: Vec<FreeTerm> = Vec::new();
        for node in self.0.iter().rev() {
            match *node {
                Node::Var(ref name) => built.push(FreeTerm::var(name.clone())),
                Node::Op(ref name, Arity(count)) => {
                    let split = built.len().saturating_sub(count);
                    let arguments: Vec<FreeTerm> = built.drain(split ..).rev().collect();
                    built.push(FreeTerm::op(name.clone(), arguments));
                },
            }
        }
        built.pop().unwrap_or_else(|| FreeTerm::results([]))
    }

    /// The place just past the subterm starting at `at`.
    ///
    /// # Specification
    /// - ensures: the end of the subterm at `at`, or the table's end when the
    ///   table runs out first.
    /// - panics: none.
    ///
    /// # Termination
    /// Every pass reads one node further along the finite table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[spec(ensures: |ret| ret.0 <= self.0.len())]
    fn end(
        &self,
        at: Place,
    ) -> Place
    {
        let mut owed: usize = 1;
        let mut here = at.0;
        while owed > 0 {
            let Some(node) = self.0.get(here)
            else {
                return Place(self.0.len());
            };
            let arity = match *node {
                Node::Var(_) => 0,
                Node::Op(_, Arity(count)) => count,
            };
            owed = owed.saturating_sub(1).saturating_add(arity);
            here = here.saturating_add(1);
        }
        Place(here)
    }

    /// The place `steps` reaches from the root, each step a child's index.
    ///
    /// # Specification
    /// - ensures: the root for no step; each step descends to the child of its
    ///   index.
    /// - fails: none when a step leaves the term.
    /// - panics: none.
    ///
    /// # Termination
    /// The outer loop reads each finite step once, the inner one skips at
    /// most the step's index of siblings.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|place| place.0 < self.0.len()))]
    fn locate(
        &self,
        steps: &[PositionStep],
    ) -> Option<Place>
    {
        let mut here = Place(0);
        for &step in steps {
            let Some(&Node::Op(_, Arity(count))) = self.0.get(here.0)
            else {
                return None;
            };
            let index = usize::from(step);
            if index >= count {
                return None;
            }
            let mut child = Place(here.0.saturating_add(1));
            for _ in 0 .. index {
                child = self.end(child);
            }
            here = child;
        }
        Some(here)
    }

    /// Where each variable of `pattern` matches the subterm of `self` at
    /// `at`.
    ///
    /// # Specification
    /// - ensures: every variable of `pattern` bound to the bounds of the
    ///   subterm it stands over, a variable written twice over two equal
    ///   subterms; every operation of `pattern` met by the same operation.
    /// - fails: none where the pattern does not match.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop reads each node of the finite pattern once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|bound| bound.values().all(|&(start, stop)| start.0 <= stop.0 && stop.0 <= self.0.len())))]
    fn matched(
        &self,
        pattern: &Self,
        at: Place,
    ) -> Option<Matched>
    {
        let mut bound = Matched::new();
        let mut here = at;
        for node in &pattern.0 {
            match *node {
                Node::Var(ref name) => {
                    let end = self.end(here);
                    let image = self.0.get(here.0 .. end.0)?;
                    match bound.get(name) {
                        Some(&(start, stop)) => {
                            if self.0.get(start.0 .. stop.0) != Some(image) {
                                return None;
                            }
                        },
                        None => {
                            let _fresh = bound.insert(name.clone(), (here, end));
                        },
                    }
                    here = end;
                },
                Node::Op(..) => {
                    if self.0.get(here.0) != Some(node) {
                        return None;
                    }
                    here = Place(here.0.saturating_add(1));
                },
            }
        }
        Some(bound)
    }

    /// `pattern` with each variable `matched` binds replaced by its image in
    /// `self`.
    ///
    /// # Specification
    /// trivial.
    fn instance(
        &self,
        pattern: &Self,
        matched: &Matched,
    ) -> Self
    {
        let mut nodes = Vec::with_capacity(pattern.0.len());
        for node in &pattern.0 {
            if let Node::Var(ref name) = *node
                && let Some(&(start, stop)) = matched.get(name)
            {
                nodes.extend(
                    self.0
                        .get(start.0 .. stop.0)
                        .unwrap_or_default()
                        .iter()
                        .cloned(),
                );
                continue;
            }
            nodes.push(node.clone());
        }
        Self(nodes)
    }

    /// `self` with the subterm at `at` replaced by `inner`.
    ///
    /// # Specification
    /// trivial.
    fn spliced(
        &self,
        at: Place,
        inner: &[Node],
    ) -> Self
    {
        let end = self.end(at);
        let mut nodes = Vec::with_capacity(self.0.len().saturating_add(inner.len()));
        nodes.extend(self.0.get(.. at.0).unwrap_or_default().iter().cloned());
        nodes.extend(inner.iter().cloned());
        nodes.extend(self.0.get(end.0 ..).unwrap_or_default().iter().cloned());
        Self(nodes)
    }

    /// The subterm at `at`.
    ///
    /// # Specification
    /// trivial.
    fn subterm(
        &self,
        at: Place,
    ) -> Self
    {
        Self(
            self.0
                .get(at.0 .. self.end(at).0)
                .unwrap_or_default()
                .to_vec(),
        )
    }
}

/// A cell of the theory's store as a rewrite of [`Flat`] terms, and what
/// firing it states in a model.
#[derive(Clone, Debug)]
struct Rule
{
    /// The left side.
    lhs: Flat,
    /// The right side.
    rhs: Flat,
    /// What firing it is: a law, a derived cell, or a cell that states
    /// nothing a model keeps.
    firing: Firing,
}

/// What firing a [`Rule`] is.
#[derive(Clone, Debug)]
enum Firing
{
    /// The written law of this name, and whether the cell runs against it.
    Law(Name, bool),
    /// The cell completion derived.
    Derived(CellId),
    /// A cell no law states.
    Unstated,
}

/// The sorts a plan reads: each operation's result sort, and each variable's.
#[derive(Clone, Debug, Default)]
struct Sorts
{
    /// Each operation's or constant's result sort, by its name.
    operations: BTreeMap<Name, Name>,
    /// Each variable's sort, by its name.
    variables: BTreeMap<Name, Name>,
}

impl Sorts
{
    /// The sort of the subterm of `term` at `at`.
    ///
    /// # Specification
    /// - ensures: a variable's sort, or an operation's result sort.
    /// - fails: none for a name neither table holds.
    /// - panics: none.
    /// - executable: none — the result is the lookup itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    fn at(
        &self,
        term: &Flat,
        at: Place,
    ) -> Option<Name>
    {
        match *term.0.get(at.0)? {
            Node::Var(ref name) => self.variables.get(name).cloned(),
            Node::Op(ref name, _) => self.operations.get(name).cloned(),
        }
    }

    /// The same sorts, each variable of `telescope` read at its binder's sort
    /// in place of any earlier reading.
    ///
    /// # Specification
    /// trivial.
    fn under(
        &self,
        telescope: &[Binder],
    ) -> Self
    {
        let mut variables = BTreeMap::new();
        for binder in telescope {
            let _fresh = variables.insert(binder.name.clone(), binder.sort.sort.clone());
        }
        Self {
            operations: self.operations.clone(),
            variables,
        }
    }
}

/// What [`plan`] reads of a theory: its members, the store's rules by cell,
/// the derived rules' certificates by cell, and the operations' sorts.
struct Theory<'cells>
{
    /// The theory's members.
    members: Members,
    /// Each cell of the presented store as a rewrite, by its cell.
    rules: Vec<Rule>,
    /// Each derived cell's certificate, by its cell.
    certificates: BTreeMap<CellId, &'cells crate::coincide::DerivedRule<TermAlphabet>>,
    /// The operations' sorts.
    sorts: Sorts,
    /// Each constant, by its sort, the first the theory declares.
    constants: BTreeMap<Name, Name>,
}

/// The proof that `left` and `right` are equal in every model of the theory
/// `presentation` presents, whose cells `cells` holds: one lemma per derived
/// cell the proof fires, in the order completion derived them, then the
/// statement's own, named `name` and written at `named`.
///
/// # Specification
/// - requires: `cells` is the cell report of the declaration presenting
///   `presentation`.
/// - ensures: each lemma's law is the law the theory's derivation states for
///   its sides; the statement's lemma last, its first leg rewriting `left` to
///   its normal form and its second the same from `right`, read back; a derived
///   cell's lemma, its certificate's path to the cell's left side read back,
///   then its path to the right side; every step fires a law or an earlier
///   lemma of the plan.
/// - fails: as [`DeriveFault`] names.
/// - panics: none.
///
/// # Errors
/// [`DeriveFault`].
///
/// # Termination
/// Each side rewrites at most [`STEPS`] times; the worklist takes each derived
/// cell of the finite store once.
///
/// # Adequacy
/// - hypothesis: L3 — a group's inverse of a product is planned over the lemmas
///   its completion derived, two sides kept apart are refused, and a side
///   naming no operation is refused.
/// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
/// - witness: `derive::tests::sides_the_completion_keeps_apart_are_refused`
/// - witness: `derive::tests::a_side_naming_no_operation_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |lemmas| !lemmas.is_empty()))]
pub(crate) fn plan(
    (name, named): (&Name, Placed),
    (left, right): (&FreeTerm, &FreeTerm),
    presentation: &Presentation,
    cells: &DeclarationCells,
) -> Result<Vec<Lemma>, DeriveFault>
{
    let theory = Theory::read(presentation, cells)?;
    let statement = theory.law(name, named, left, right)?;
    let ModelForm::Law { ref telescope, .. } = statement
    else {
        return Err(DeriveFault::Unsorted(ModelFault::UnknownHead));
    };
    let sorts = theory.sorts.under(telescope);
    let (Some(left), Some(right)) = (Flat::of(left), Flat::of(right))
    else {
        return Err(DeriveFault::Unsorted(ModelFault::Constructor));
    };
    let (left_normal, left_fired) = theory.normalise(left.clone())?;
    let (right_normal, right_fired) = theory.normalise(right.clone())?;
    if left_normal != right_normal {
        return Err(DeriveFault::Apart);
    }
    let needed = theory.needed(left_fired.iter().chain(&right_fired).map(|&(_, cell)| cell))?;
    let places: BTreeMap<CellId, LemmaIndex> = needed
        .iter()
        .enumerate()
        .map(|(place, &cell)| (cell, LemmaIndex(place)))
        .collect();
    let mut lemmas = Vec::with_capacity(needed.len().saturating_add(1));
    for &cell in &needed {
        lemmas.push(theory.lemma(cell, (name, named), &places)?);
    }
    let first = theory.fired(&left, &left_fired, &sorts, &places)?;
    let second = theory.fired(&right, &right_fired, &sorts, &places)?;
    lemmas.push(Lemma {
        law: statement,
        legs: [
            Leg {
                from: left.free(),
                steps: first,
                back: false,
            },
            Leg {
                from: right.free(),
                steps: second,
                back: true,
            },
        ],
    });

    Ok(lemmas)
}

impl<'cells> Theory<'cells>
{
    /// What [`plan`] reads of the theory `presentation` presents, whose cells
    /// `cells` holds.
    ///
    /// # Specification
    /// - ensures: one rule per cell of the presented store, a written cell
    ///   firing the law whose sides it spells, either way round, and a derived
    ///   one its own lemma; every derived rule's certificate by its cell.
    /// - fails: [`DeriveFault::Indexed`] for an indexed sort or a nested model;
    ///   [`DeriveFault::Unstated`] for a component the models cannot state;
    ///   [`DeriveFault::Incoherent`] for a value coding no presentation or
    ///   rules the coherence check refused or did not examine.
    /// - panics: none.
    /// - executable: none — the reading is checked through the plan it feeds.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    fn read(
        presentation: &Presentation,
        cells: &'cells DeclarationCells,
    ) -> Result<Self, DeriveFault>
    {
        let members = presentation
            .members()
            .map_err(|_unpresented| DeriveFault::Incoherent)?;
        let signature = derive_members(&members, &presentation.circuits);
        let mut sorts = Sorts::default();
        let mut constants = BTreeMap::new();
        for component in &signature.components {
            match component.form {
                Ok(ModelForm::Sort { ref indices }) => {
                    if !indices.is_empty() {
                        return Err(DeriveFault::Indexed);
                    }
                },
                Ok(ModelForm::Nested(_)) => return Err(DeriveFault::Indexed),
                Ok(ModelForm::Operation { ref results, .. }) => {
                    if let [ref result] = *results.as_slice() {
                        let _fresh = sorts
                            .operations
                            .insert(component.name.clone(), result.sort.clone());
                    }
                },
                Ok(ModelForm::Constant(ref sort)) => {
                    let _fresh = sorts
                        .operations
                        .insert(component.name.clone(), sort.sort.clone());
                    let _first = constants
                        .entry(sort.sort.clone())
                        .or_insert_with(|| component.name.clone());
                },
                Ok(ModelForm::Law { .. }) => {},
                Err(fault) => return Err(DeriveFault::Unstated(fault)),
            }
        }
        let certificates = match cells.coincidence {
            Coincidence::Joined(ref certificates) => certificates
                .derived_terms
                .iter()
                .map(|derived| (derived.cell, derived))
                .collect(),
            Coincidence::Orthogonal => BTreeMap::new(),
            Coincidence::Unexamined | Coincidence::Refused(_) => {
                return Err(DeriveFault::Incoherent);
            },
        };
        let mut rules = Vec::new();
        if let Maybe::Present(ref presented) = cells.presented {
            for (cell, stored) in presented.store.iter() {
                let sides = match (stored.lhs().read(), stored.rhs().read()) {
                    (Maybe::Present(lhs), Maybe::Present(rhs)) => {
                        Flat::of(&lhs).zip(Flat::of(&rhs))
                    },
                    (
                        Maybe::Present(_) | Maybe::Absent(_),
                        Maybe::Present(_) | Maybe::Absent(_),
                    ) => None,
                };
                let Some((lhs, rhs)) = sides
                else {
                    return Err(DeriveFault::Incoherent);
                };
                let firing = match stored.provenance() {
                    TermProv::Derived => Firing::Derived(cell),
                    TermProv::SurfaceRule => members
                        .laws
                        .iter()
                        .find_map(|law| {
                            let written = (Flat::of(&law.left)?, Flat::of(&law.right)?);
                            if written.0 == lhs && written.1 == rhs {
                                Some(Firing::Law(law.name.clone(), false))
                            }
                            else if written.0 == rhs && written.1 == lhs {
                                Some(Firing::Law(law.name.clone(), true))
                            }
                            else {
                                None
                            }
                        })
                        .unwrap_or(Firing::Unstated),
                };
                rules.push(Rule { lhs, rhs, firing });
            }
        }

        Ok(Self {
            members,
            rules,
            certificates,
            sorts,
            constants,
        })
    }

    /// The law `left <=> right` states over the theory, named `name` and
    /// written at `named`.
    ///
    /// # Specification
    /// - ensures: the law [`derive_laws`] derives for the two sides.
    /// - fails: [`DeriveFault::Unsorted`] with the derivation's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    /// - witness: `derive::tests::a_side_naming_no_operation_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |form| matches!(*form, ModelForm::Law { .. })))]
    fn law(
        &self,
        name: &Name,
        named: Placed,
        left: &FreeTerm,
        right: &FreeTerm,
    ) -> Result<ModelForm, DeriveFault>
    {
        let law = PresentedLaw {
            name: name.clone(),
            named,
            left: left.clone(),
            right: right.clone(),
        };
        match derive_laws(&self.members, &[law]).pop() {
            Some(Ok(form)) => Ok(form),
            Some(Err(fault)) => Err(DeriveFault::Unsorted(fault)),
            None => Err(DeriveFault::Unsorted(ModelFault::UnknownHead)),
        }
    }

    /// `term`'s normal form, and each step that reaches it: the place it
    /// fires at and the cell it fires.
    ///
    /// # Specification
    /// - ensures: each step fires the first cell, in store order, whose left
    ///   side matches at the first place, in prefix order, any matches; the
    ///   normal form is the term no cell matches anywhere.
    /// - fails: [`DeriveFault::Undecided`] past [`STEPS`] steps.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Termination
    /// At most [`STEPS`] steps, each scanning the finite term's places and the
    /// finite store once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    /// - witness: `derive::tests::sides_the_completion_keeps_apart_are_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(_, ref fired)| fired.len() <= STEPS))]
    fn normalise(
        &self,
        mut term: Flat,
    ) -> Result<(Flat, Vec<(Place, CellId)>), DeriveFault>
    {
        let mut fired = Vec::new();
        'steps: for _ in 0 .. STEPS {
            for place in 0 .. term.0.len() {
                for (cell, rule) in self.rules.iter().enumerate() {
                    let Some(matched) = term.matched(&rule.lhs, Place(place))
                    else {
                        continue;
                    };
                    let contractum = term.instance(&rule.rhs, &matched);
                    term = term.spliced(Place(place), &contractum.0);
                    fired.push((Place(place), CellId::from(cell)));
                    continue 'steps;
                }
            }
            return Ok((term, fired));
        }
        Err(DeriveFault::Undecided)
    }

    /// Every derived cell `fired` names, and every derived cell the
    /// certificates of those name, in the order completion derived them.
    ///
    /// # Specification
    /// - ensures: the least set holding each derived cell of `fired` and, with
    ///   a cell, each derived cell either path of its certificate fires.
    /// - fails: [`DeriveFault::Incoherent`] for a derived cell with no
    ///   certificate.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Termination
    /// Each derived cell of the finite store enters the worklist once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |needed| needed.iter().all(|cell| self.certificates.contains_key(cell))))]
    fn needed(
        &self,
        fired: impl Iterator<Item = CellId>,
    ) -> Result<BTreeSet<CellId>, DeriveFault>
    {
        let mut needed = BTreeSet::new();
        let mut pending: Vec<CellId> = fired.collect();
        while let Some(cell) = pending.pop() {
            let Some(&Rule {
                firing: Firing::Derived(_),
                ..
            }) = self.rules.get(usize::from(cell))
            else {
                continue;
            };
            if !needed.insert(cell) {
                continue;
            }
            let derived = self
                .certificates
                .get(&cell)
                .ok_or(DeriveFault::Incoherent)?;
            let certificate = &derived.certificate;
            pending.extend(
                certificate
                    .path_a
                    .iter()
                    .chain(&certificate.path_b)
                    .map(|step| step.cell)
                    .filter(|&step| step != cell),
            );
        }
        Ok(needed)
    }

    /// The lemma of the derived cell `cell`: its law, named `name` and
    /// written at `named`, proved by its certificate, each derived cell the
    /// proof fires read at its place of `places`.
    ///
    /// # Specification
    /// - ensures: as [`plan`] states a derived cell's lemma; a variable of the
    ///   peak neither side keeps reads as the first variable of the law of its
    ///   sort, or else the theory's first constant of its sort.
    /// - fails: [`DeriveFault::Erased`] for a variable no such term stands for;
    ///   [`DeriveFault::Incoherent`] for a certificate that does not end at the
    ///   cell's sides; the faults [`Self::fired`] yields.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: one search of the law's few binders per variable of the peak"
        )
    )]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |lemma| matches!(lemma.law, ModelForm::Law { .. })))]
    fn lemma(
        &self,
        cell: CellId,
        (name, named): (&Name, Placed),
        places: &BTreeMap<CellId, LemmaIndex>,
    ) -> Result<Lemma, DeriveFault>
    {
        let rule = self
            .rules
            .get(usize::from(cell))
            .ok_or(DeriveFault::Incoherent)?;
        let derived = self
            .certificates
            .get(&cell)
            .ok_or(DeriveFault::Incoherent)?;
        let (lhs, rhs) = (rule.lhs.free(), rule.rhs.free());
        let law = self.law(name, named, &lhs, &rhs)?;
        let ModelForm::Law { ref telescope, .. } = law
        else {
            return Err(DeriveFault::Unsorted(ModelFault::UnknownHead));
        };
        let Maybe::Present(peak) = derived.certificate.overlap.peak.read()
        else {
            return Err(DeriveFault::Incoherent);
        };
        let ModelForm::Law {
            telescope: ref read,
            ..
        } = self.law(name, named, &peak, &peak)?
        else {
            return Err(DeriveFault::Unsorted(ModelFault::UnknownHead));
        };
        let mut erased = BTreeMap::new();
        for binder in read {
            if telescope.iter().any(|kept| kept.name == binder.name) {
                continue;
            }
            let stands = telescope
                .iter()
                .find(|kept| kept.sort == binder.sort)
                .map(|kept| Node::Var(kept.name.clone()))
                .or_else(|| {
                    self.constants
                        .get(&binder.sort.sort)
                        .map(|constant| Node::Op(constant.clone(), Arity(0)))
                })
                .ok_or(DeriveFault::Erased)?;
            let _fresh = erased.insert(binder.name.clone(), stands);
        }
        let peak = Flat::of(&peak).ok_or(DeriveFault::Incoherent)?;
        let peak = Flat(
            peak.0
                .into_iter()
                .map(|node| match node {
                    Node::Var(name) => erased.get(&name).cloned().unwrap_or(Node::Var(name)),
                    Node::Op(..) => node,
                })
                .collect(),
        );
        let fires = |path: &[CellApp<TermAlphabet>]| {
            path.last()
                .is_some_and(|step| step.cell == cell && step.at.steps().is_empty())
        };
        let certificate = &derived.certificate;
        let (deriving, other) = if fires(&certificate.path_a) {
            (&certificate.path_a, &certificate.path_b)
        }
        else if fires(&certificate.path_b) {
            (&certificate.path_b, &certificate.path_a)
        }
        else {
            return Err(DeriveFault::Incoherent);
        };
        let deriving = deriving.split_last().map_or(&[][..], |(_, before)| before);
        let sorts = self.sorts.under(telescope);
        let located = |path: &[CellApp<TermAlphabet>]| -> Result<_, DeriveFault> {
            let mut term = peak.clone();
            let mut steps = Vec::with_capacity(path.len());
            for app in path {
                let place = term.locate(app.at.steps()).ok_or(DeriveFault::Incoherent)?;
                let (step, after) = self.step(&term, place, app.cell, &sorts, places)?;
                steps.push(step);
                term = after;
            }
            Ok((steps, term))
        };
        let (first, reached) = located(deriving)?;
        let (second, joined) = located(other)?;
        if reached != rule.lhs || joined != rule.rhs {
            return Err(DeriveFault::Incoherent);
        }

        Ok(Lemma {
            law,
            legs: [
                Leg {
                    from: peak.free(),
                    steps: first,
                    back: true,
                },
                Leg {
                    from: peak.free(),
                    steps: second,
                    back: false,
                },
            ],
        })
    }

    /// The steps `fired` takes from `term`, each read under `sorts` and each
    /// derived cell at its place of `places`.
    ///
    /// # Specification
    /// - ensures: one step per fired cell, in order, each from the term the one
    ///   before reached.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |steps| steps.len() == fired.len()))]
    fn fired(
        &self,
        term: &Flat,
        fired: &[(Place, CellId)],
        sorts: &Sorts,
        places: &BTreeMap<CellId, LemmaIndex>,
    ) -> Result<Vec<Step>, DeriveFault>
    {
        let mut term = term.clone();
        let mut steps = Vec::with_capacity(fired.len());
        for &(place, cell) in fired {
            let (step, after) = self.step(&term, place, cell, sorts, places)?;
            steps.push(step);
            term = after;
        }
        Ok(steps)
    }

    /// The step firing `cell` at `at` in `term`, and the term it reaches.
    ///
    /// # Specification
    /// - ensures: the step's context is `term` with [`HOLE`] at `at`, its redex
    ///   the subterm at `at` and the cell's right side under the match of its
    ///   left side there; a written cell fires its law, a derived one its place
    ///   of `places`.
    /// - fails: [`DeriveFault::Incoherent`] where the cell does not match, is
    ///   no cell of the store, states no law, or is a derived cell `places`
    ///   does not hold; [`DeriveFault::Unsorted`] for a subterm whose sort
    ///   `sorts` does not read.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`plan`].
    /// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ref step, ref after)| step.whole.1 == after.free()))]
    fn step(
        &self,
        term: &Flat,
        at: Place,
        cell: CellId,
        sorts: &Sorts,
        places: &BTreeMap<CellId, LemmaIndex>,
    ) -> Result<(Step, Flat), DeriveFault>
    {
        let rule = self
            .rules
            .get(usize::from(cell))
            .ok_or(DeriveFault::Incoherent)?;
        let matched = term.matched(&rule.lhs, at).ok_or(DeriveFault::Incoherent)?;
        let fired = match rule.firing {
            Firing::Law(ref name, backward) => Fired::Law {
                name: name.clone(),
                backward,
            },
            Firing::Derived(derived) => {
                Fired::Lemma(*places.get(&derived).ok_or(DeriveFault::Incoherent)?)
            },
            Firing::Unstated => return Err(DeriveFault::Incoherent),
        };
        let contractum = term.instance(&rule.rhs, &matched);
        let after = term.spliced(at, &contractum.0);
        let unsorted = DeriveFault::Unsorted(ModelFault::Unsorted);
        let redex_sort = sorts.at(term, at).ok_or(unsorted)?;
        let whole_sort = sorts.at(term, Place(0)).ok_or(unsorted)?;
        let substitution = matched
            .iter()
            .map(|(name, &(start, stop))| {
                let image = Flat(term.0.get(start.0 .. stop.0).unwrap_or_default().to_vec());
                (name.clone(), image.free())
            })
            .collect();
        let context = term.spliced(at, &[Node::Var(Name::from(HOLE))]);
        let step = Step {
            fired,
            context: context.free(),
            redex: (term.subterm(at).free(), contractum.free()),
            whole: (term.free(), after.free()),
            substitution,
            sorts: (redex_sort, whole_sort),
        };

        Ok((step, after))
    }
}

#[cfg(test)]
mod tests;
