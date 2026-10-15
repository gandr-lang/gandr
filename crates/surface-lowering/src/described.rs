//! The types a described declaration's members state, each at the node the
//! source writes it at, for a face answering a reader who points there.
//!
//! # A member answers at what it states
//!
//! A `sign` block, and a `data` family's constructors and its `oper` and
//! `rule` members, write no term the typed run judges: the description route
//! reads them ([`crate::description`]). It states their types here, in the core
//! vocabulary every face spells through, at the bytes
//! [`crate::description::written`] keeps for each node:
//!
//! - **A sign** reads as the telescope `Model(S)` lays its components out in
//!   ([`crate::model`]): each sort a binder of its kind — `Type`, or for an
//!   indexed sort the arrow from its indices into `Type` — and each operation a
//!   binder of the type its component states, under the components before it. A
//!   written sort is the decode of its code. A sort's or an operation's name
//!   answers at that kind or type; a law's name at the `Path` type its
//!   component states, under every sort and operation; a port's name and an
//!   index's at its sort; each node of a law's sides at its sort, its variables
//!   bound by the law's telescope; an operation's head at the operation's type;
//!   each written sort at its universe, and the classifier `Type` at its own;
//!   and a circuit's ports and wires at the sort the ports they meet read,
//!   where that sort is one the sign declares unindexed.
//! - **A data family's** constructors, operations and rules read over the
//!   module's own unparameterised families: a constant constructor's name
//!   answers at its family, one with fields at `+U (A₁ -> … -> -F F)`, each
//!   field's name at its type; an operation's name at `+U (A₁ -> … -> -F B)`,
//!   `B` the product of the results when there are several, as the operation
//!   runs (`crate::operation`); each port's name at its sort and each written
//!   sort at the family's universe; each node of a rule's sides at its sort —
//!   an application of an operation at its result, of a constructor at its
//!   family, a variable at the sort of the position it is first written in —
//!   and an operation's head at its type.
//! - **A parameterised data family's** constructors read under its parameters:
//!   each name at the type above with `F` applied to them, each field's name at
//!   its type, the written result at the family's universe and each argument
//!   naming a parameter at that parameter's classifier.
//!
//! A component the derivation cannot state answers nowhere, and neither does
//! a node no position sorts.
//!
//! - Choice: read a sign as a telescope of variables, its sorts codes in
//!   `Type`, so each member answers at the type `Model(S)` derives, spelled by
//!   the names the sign writes. Alternatives: a nominal atom per sort, which
//!   the core keeps for sealed abstract types alone and no constant of the
//!   module names; and the presentation spelled as text, which bypasses the
//!   printer every face shares. Reversal: a sign's `Model(S)` components
//!   lowered to core declarations of their own — beside the value `S : Sig` the
//!   block already defines — which a face then reads as it reads any other.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use crate::DeclarationOutcome;
use crate::description::DescriptionGrade;
use crate::description::FamilyParameter;
use crate::description::written::WrittenCircuit;
use crate::description::written::WrittenMembers;
use crate::description::written::WrittenPort;
use crate::description::written::WrittenSort;
use crate::description::written::WrittenTerm;
use crate::model::Binder;
use crate::model::Dependent;
use crate::model::Members;
use crate::model::ModelForm;
use crate::model::Presentation;
use crate::model::SortTerm;
use crate::model::Tail;
use crate::model::dependence;
use crate::model::derive_members;
use crate::module::LoweredModule;

/// What a described node is, for a face reading it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DescribedRole
{
    /// A name a member or a port declares, at the type it declares.
    Name,
    /// A term a rule or a circuit writes, at its sort.
    Term,
    /// A written sort, at its universe.
    Type,
}

/// The place of a context in [`DescribedTypes::contexts`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContextIndex(usize);

impl From<ContextIndex> for usize
{
    /// The place, as an index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ContextIndex) -> Self
    {
        index.0
    }
}

/// One described node and the type it answers at.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DescribedType
{
    /// The bytes the node covers.
    pub span: ByteSpan,
    /// What the node is.
    pub role: DescribedRole,
    /// Its type, in the arena it was minted into.
    pub ty: ValueTypeId,
    /// The context the type is read in.
    pub context: ContextIndex,
}

/// Every described node's type, and the contexts they are read in.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DescribedTypes
{
    /// The nodes, in source order of their members.
    pub entries: Vec<DescribedType>,
    /// Each context: the names its binders are written under, outermost
    /// first; the first context is the empty one.
    pub contexts: Vec<Vec<Name>>,
}

/// One binder of the scope a type is minted under.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Bound
{
    /// The name it binds.
    name: Name,
    /// Whether it binds a variable of the core context.
    binds: Dependent,
}

/// The scope a type is minted under, outermost first.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
struct Scope
{
    /// The binders.
    binders: Vec<Bound>,
}

impl Scope
{
    /// The index of the variable `name` under this scope: for its innermost
    /// binder, when it binds, the count of binding binders after it.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        &self,
        name: &Name,
    ) -> Option<DeBruijnIndex>
    {
        let at = self.binders.iter().rposition(|bound| bound.name == *name)?;
        if !self.binders.get(at)?.binds.0 {
            return None;
        }
        let after = self
            .binders
            .get(at.saturating_add(1) ..)?
            .iter()
            .filter(|bound| bound.binds.0)
            .count();
        u32::try_from(after).ok().map(DeBruijnIndex::from)
    }

    /// Bind `name`.
    ///
    /// # Specification
    /// trivial.
    fn push(
        &mut self,
        name: &Name,
        binds: Dependent,
    )
    {
        self.binders.push(Bound {
            name: name.clone(),
            binds,
        });
    }

    /// The names of the binding binders, outermost first.
    ///
    /// # Specification
    /// trivial.
    fn names(&self) -> Vec<Name>
    {
        self.binders
            .iter()
            .filter(|bound| bound.binds.0)
            .map(|bound| bound.name.clone())
            .collect()
    }
}

/// What a telescope's type returns.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Codomain<'form>
{
    /// The universe `Type`: a sort's kind.
    Universe,
    /// An operation's results, their product when there are several.
    Results(&'form [SortTerm]),
    /// A law's path between its endpoints.
    Path(&'form SortTerm, &'form FreeTerm, &'form FreeTerm),
}

/// One step of the walk minting a term's value.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Step<'term>
{
    /// A node whose value is minted next.
    Read(TermNode<'term>),
    /// The named operation applied to this many values last minted.
    Apply(&'term Name, usize),
}

/// One step of the walk substituting a term.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Rebuild<'term>
{
    /// A node to rebuild.
    Read(TermNode<'term>),
    /// An operation over this many terms last rebuilt.
    Op(&'term Name, usize),
    /// A constructor over this many terms last rebuilt.
    Ctor(&'term Name, usize),
    /// A results tuple of this many terms last rebuilt.
    Results(usize),
}

/// A data family's operation, read over the module's families.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Operation
{
    /// Its inputs' types.
    inputs: Vec<ValueTypeId>,
    /// Its result: the one output's type, or the product of several.
    result: ValueTypeId,
    /// Its type, `+U (A₁ -> … -> -F B)`.
    ty: ValueTypeId,
}

/// The minting of every described node's type into one arena.
///
/// # Specification
/// trivial.
struct Typer<'arena>
{
    /// The arena the types are minted into.
    arena: &'arena mut CoreArena,
    /// What has been minted.
    types: DescribedTypes,
}

/// `term` with each variable `by` names replaced by the term it maps to.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the term's shape, every variable leaf `by` holds its image; the
///   term itself when `by` holds nothing.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Each node of the finite term is read once and rebuilt once.
///
/// # Adequacy
/// - hypothesis: L3 — `comp`'s result `Hom(a, c)` reads `Hom(a, b)` under the
///   law `unitL`'s elaborated arguments.
/// - witness: `described::tests::a_sign_answers_at_every_member`
#[spec(ensures: |ret| !by.is_empty() || ret.eq(term))]
fn substitute(
    term: &FreeTerm,
    by: &BTreeMap<&Name, &FreeTerm>,
) -> FreeTerm
{
    let mut pending = Vec::from([Rebuild::Read(term.to_node())]);
    let mut built: Vec<FreeTerm> = Vec::new();
    let take = |built: &mut Vec<FreeTerm>, count: usize| {
        let start = built.len().saturating_sub(count);
        built.drain(start ..).collect::<Vec<_>>()
    };
    while let Some(step) = pending.pop() {
        match step {
            Rebuild::Read(node) => match node.view() {
                TermView::Var(name) => built.push(
                    by.get(name)
                        .map_or_else(|| FreeTerm::var(name.clone()), |&image| image.clone()),
                ),
                TermView::Op { name, args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Rebuild::Op(name, args.len()));
                    pending.extend(args.into_iter().rev().map(Rebuild::Read));
                },
                TermView::Ctor { name, args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Rebuild::Ctor(name, args.len()));
                    pending.extend(args.into_iter().rev().map(Rebuild::Read));
                },
                TermView::Results { args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Rebuild::Results(args.len()));
                    pending.extend(args.into_iter().rev().map(Rebuild::Read));
                },
            },
            Rebuild::Op(name, count) => {
                let args = take(&mut built, count);
                built.push(FreeTerm::op(name.clone(), args));
            },
            Rebuild::Ctor(name, count) => {
                let args = take(&mut built, count);
                built.push(FreeTerm::ctor(name.clone(), args));
            },
            Rebuild::Results(count) => {
                let args = take(&mut built, count);
                built.push(FreeTerm::results(args));
            },
        }
    }
    built.pop().unwrap_or_else(|| term.clone())
}

impl Typer<'_>
{
    /// The context `scope` reads in, recorded once.
    ///
    /// # Specification
    /// trivial.
    fn context(
        &mut self,
        scope: &Scope,
    ) -> ContextIndex
    {
        let names = scope.names();
        if let Some(at) = self.types.contexts.iter().position(|held| *held == names) {
            return ContextIndex(at);
        }
        self.types.contexts.push(names);
        ContextIndex(self.types.contexts.len().saturating_sub(1))
    }

    /// Record the node at `span` as `role` at `ty`, read in `context`.
    ///
    /// # Specification
    /// trivial.
    fn emit(
        &mut self,
        span: ByteSpan,
        role: DescribedRole,
        ty: ValueTypeId,
        context: ContextIndex,
    )
    {
        self.types.entries.push(DescribedType {
            span,
            role,
            ty,
            context,
        });
    }

    /// The value universe at `level`.
    ///
    /// # Specification
    /// trivial.
    fn universe(
        &mut self,
        level: Level,
    ) -> ValueTypeId
    {
        self.arena
            .value_type_universe(Sort::Ground(GroundSort::Value), level)
    }

    /// The value `term` denotes under `scope`: a variable its index, an
    /// application `g(t₁, …)` the returned call `↑((force g) t₁ …)` of the
    /// variable `g` names; none for a constructor, a results tuple or a name
    /// the scope does not bind.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        scope: &Scope,
        term: &FreeTerm,
    ) -> Option<ValueId>
    {
        let mut pending = Vec::from([Step::Read(term.to_node())]);
        let mut built: Vec<ValueId> = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                Step::Read(node) => match node.view() {
                    TermView::Var(name) => {
                        let index = scope.variable(name)?;
                        built.push(self.arena.value_variable(Zone::Intuitionistic, index));
                    },
                    TermView::Op { name, args } => {
                        let args: Vec<TermNode<'_>> = args.collect();
                        pending.push(Step::Apply(name, args.len()));
                        pending.extend(args.into_iter().rev().map(Step::Read));
                    },
                    TermView::Ctor { .. } | TermView::Results { .. } => return None,
                },
                Step::Apply(name, count) => {
                    let start = built.len().checked_sub(count)?;
                    let arguments: Vec<ValueId> = built.drain(start ..).collect();
                    let applied = self.apply(scope, name, &arguments)?;
                    built.push(applied);
                },
            }
        }
        match *built.as_slice() {
            [value] => Some(value),
            _ => None,
        }
    }

    /// The returned call of the variable `head` names on `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn apply(
        &mut self,
        scope: &Scope,
        head: &Name,
        arguments: &[ValueId],
    ) -> Option<ValueId>
    {
        let index = scope.variable(head)?;
        let head = self.arena.value_variable(Zone::Intuitionistic, index);
        let mut applied = self.arena.computation_force(head);
        for &argument in arguments {
            applied = self.arena.computation_application(applied, argument);
        }
        Some(self.arena.value_returned(applied))
    }

    /// The type the sort term `sort` names under `scope`: the decode of the
    /// sort's code, applied to its indices' values.
    ///
    /// # Specification
    /// trivial.
    fn sort(
        &mut self,
        scope: &Scope,
        sort: &SortTerm,
    ) -> Option<ValueTypeId>
    {
        let code = if sort.indices.is_empty() {
            let index = scope.variable(&sort.sort)?;
            self.arena.value_variable(Zone::Intuitionistic, index)
        }
        else {
            let mut values = Vec::with_capacity(sort.indices.len());
            for index in &sort.indices {
                values.push(self.value(scope, index)?);
            }
            self.apply(scope, &sort.sort, &values)?
        };
        Some(self.arena.value_type_element(code, Level::zero()))
    }

    /// The type of a telescope over `telescope` returning `codomain`, minted
    /// under `scope` as `Model(S)` states it: `+U` over one binder per entry,
    /// dependent exactly where `tail` or a later entry names it.
    ///
    /// # Specification
    /// - requires: `tail` names what `codomain` mints.
    /// - ensures: the thunk of the chain of Π and arrows over each entry's sort
    ///   into the returner of the codomain; `scope` as it was.
    /// - fails: none when a sort or a term names what the scope does not bind.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp`'s three object binders bind and its two
    ///   morphisms do not; `unitL`'s law relates two applications.
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    #[spec(captures: before = scope.binders.len(), ensures: scope.binders.len() == before)]
    fn telescope(
        &mut self,
        scope: &mut Scope,
        telescope: &[Binder],
        tail: Tail<'_>,
        codomain: Codomain<'_>,
    ) -> Option<ValueTypeId>
    {
        let dependent = dependence(telescope, tail);
        let base = scope.binders.len();
        let minted = self.chain(scope, telescope, &dependent, codomain);
        scope.binders.truncate(base);
        minted
    }

    /// The body of [`Self::telescope`], leaving the binders it pushes on
    /// `scope`.
    ///
    /// # Specification
    /// trivial.
    fn chain(
        &mut self,
        scope: &mut Scope,
        telescope: &[Binder],
        dependent: &[Dependent],
        codomain: Codomain<'_>,
    ) -> Option<ValueTypeId>
    {
        let mut domains = Vec::with_capacity(telescope.len());
        for (binder, &binds) in telescope.iter().zip(dependent) {
            domains.push(self.sort(scope, &binder.sort)?);
            scope.push(&binder.name, binds);
        }
        let result = match codomain {
            Codomain::Universe => self.universe(Level::zero()),
            Codomain::Results(results) => {
                let mut sorts = Vec::with_capacity(results.len());
                for result in results {
                    sorts.push(self.sort(scope, result)?);
                }
                match *sorts.as_slice() {
                    [one] => one,
                    _ => self.arena.value_type_product(&sorts),
                }
            },
            Codomain::Path(carrier, left, right) => {
                let over = self.sort(scope, carrier)?;
                let from = self.value(scope, left)?;
                let to = self.value(scope, right)?;
                self.arena.value_type_path(over, from, to)
            },
        };
        let mut chain = self.arena.comp_type_returner(result);
        for (&domain, binds) in domains.iter().zip(dependent).rev() {
            chain = if binds.0 {
                self.arena.comp_type_pi(domain, chain)
            }
            else {
                self.arena.comp_type_arrow(domain, chain)
            };
        }
        Some(self.arena.value_type_thunk(chain))
    }

    /// Record a written sort at the universe its sorts are coded in, when its
    /// head is one of `sorts`.
    ///
    /// # Specification
    /// trivial.
    fn occurrence(
        &mut self,
        written: &WrittenSort,
        head: &Name,
        sorts: &[Name],
    )
    {
        if sorts.contains(head) {
            let universe = self.universe(Level::zero());
            let closed = self.context(&Scope::default());
            self.emit(written.span, DescribedRole::Type, universe, closed);
        }
    }

    /// Record each variable of a written sort's index terms at its binder's
    /// sort among `telescope`, under `scope`.
    ///
    /// # Specification
    /// trivial.
    fn indices(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        sort: &SortTerm,
        written: &WrittenSort,
    )
    {
        let context = self.context(scope);
        for (term, nodes) in sort.indices.iter().zip(&written.indices) {
            let mut pending = Vec::from([term.to_node()]);
            let mut at = nodes.nodes.iter();
            while let Some(node) = pending.pop() {
                let Some(written) = at.next()
                else {
                    break;
                };
                match node.view() {
                    TermView::Var(name) => {
                        if let Some(binder) =
                            telescope.iter().rev().find(|binder| binder.name == *name)
                            && let Some(ty) = self.sort(scope, &binder.sort)
                        {
                            self.emit(written.span, DescribedRole::Term, ty, context);
                        }
                    },
                    TermView::Op { args, .. }
                    | TermView::Ctor { args, .. }
                    | TermView::Results { args } => {
                        let first = pending.len();
                        pending.extend(args);
                        if let Some(added) = pending.get_mut(first ..) {
                            added.reverse();
                        }
                    },
                }
            }
        }
    }

    /// Record each port of `ports`, written as `written`, the last binders of
    /// `telescope` — those before them are inserted — its name at its sort
    /// under the binders before it, its sort at its universe, and its sort's
    /// index variables.
    ///
    /// # Specification
    /// trivial.
    fn ports(
        &mut self,
        scope: &mut Scope,
        telescope: &[Binder],
        dependent: &[Dependent],
        written: &[WrittenPort],
        sorts: &[Name],
    )
    {
        let first = telescope.len().saturating_sub(written.len());
        let base = scope.binders.len();
        for (at, (binder, &binds)) in telescope.iter().zip(dependent).enumerate() {
            if let Some(port) = at.checked_sub(first).and_then(|place| written.get(place)) {
                self.port(scope, telescope, &binder.sort, port, sorts);
            }
            scope.push(&binder.name, binds);
        }
        scope.binders.truncate(base);
    }

    /// Record one port of sort `sort`, written as `port`, under `scope`.
    ///
    /// # Specification
    /// trivial.
    fn port(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        sort: &SortTerm,
        port: &WrittenPort,
        sorts: &[Name],
    )
    {
        if let Maybe::Present(named) = port.named
            && let Some(ty) = self.sort(scope, sort)
        {
            let context = self.context(scope);
            self.emit(named, DescribedRole::Name, ty, context);
        }
        self.occurrence(&port.sort, &sort.sort, sorts);
        self.indices(scope, telescope, sort, &port.sort);
    }

    /// Record every member of a sign presenting `presentation`, written as
    /// `written`.
    ///
    /// # Specification
    /// - requires: `written` is where the sign reader read `presentation`'s
    ///   members.
    /// - ensures: as the module documentation states for a sign: each sort,
    ///   operation and law at what its `Model(S)` component states, each port
    ///   at its sort, each node of a law at its sort, each written sort at its
    ///   universe, each circuit's ports and wires at their sorts.
    /// - fails: never; a presentation whose members cannot be read records
    ///   nothing, and a component the derivation cannot state records none of
    ///   the nodes its type would read.
    /// - panics: none.
    /// - executable: none — each node answers at a type minted into the arena,
    ///   which no predicate over the presentation restates; the witness reads
    ///   each back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the probe signs' sorts, operations, laws and circuit
    ///   answer at the types asserted.
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    fn sign(
        &mut self,
        presentation: &Presentation,
        written: &WrittenMembers,
    )
    {
        let Ok(members) = presentation.members()
        else {
            return;
        };
        let model = derive_members(&members, &presentation.circuits);
        let names: Vec<Name> = members.sorts.iter().map(|sort| sort.name.clone()).collect();
        let mut scope = Scope::default();
        let mut forms = model.components.iter().map(|component| &component.form);
        let closed = self.context(&Scope::default());
        for (sort, member) in members.sorts.iter().zip(&written.sorts) {
            if let Ok(level) = Level::zero().succ() {
                let universe = self.universe(level);
                self.emit(member.classifier, DescribedRole::Type, universe, closed);
            }
            if let Some(&Ok(ModelForm::Sort { ref indices })) = forms.next() {
                let tail = Tail::Results(&[]);
                let kind = if indices.is_empty() {
                    Some(self.universe(Level::zero()))
                }
                else {
                    self.telescope(&mut scope, indices, tail, Codomain::Universe)
                };
                if let Some(kind) = kind {
                    let context = self.context(&scope);
                    self.emit(member.named, DescribedRole::Name, kind, context);
                }
                let dependent = dependence(indices, tail);
                self.ports(&mut scope, indices, &dependent, &member.indices, &names);
            }
            scope.push(&sort.name, Dependent(true));
        }
        let mut heads: BTreeMap<Name, (ValueTypeId, ContextIndex)> = BTreeMap::new();
        let mut operations: BTreeMap<Name, (&[Binder], &[SortTerm])> = BTreeMap::new();
        for (operation, member) in members.operations.iter().zip(&written.operations) {
            if let Some(&Ok(ModelForm::Operation {
                ref telescope,
                ref results,
            })) = forms.next()
            {
                let tail = Tail::Results(results);
                if let Some(ty) =
                    self.telescope(&mut scope, telescope, tail, Codomain::Results(results))
                {
                    let context = self.context(&scope);
                    self.emit(member.named, DescribedRole::Name, ty, context);
                    let _first = heads.insert(operation.name.clone(), (ty, context));
                }
                let _first = operations.insert(operation.name.clone(), (telescope, results));
                let dependent = dependence(telescope, tail);
                self.ports(&mut scope, telescope, &dependent, &member.inputs, &names);
                let base = scope.binders.len();
                for (binder, &binds) in telescope.iter().zip(&dependent) {
                    scope.push(&binder.name, binds);
                }
                for (result, port) in results.iter().zip(&member.outputs) {
                    self.port(&scope, telescope, result, port, &names);
                }
                scope.binders.truncate(base);
            }
            else {
                let presented = operation.inputs.iter().chain(&operation.outputs);
                for (port, at) in presented.zip(member.inputs.iter().chain(&member.outputs)) {
                    self.occurrence(&at.sort, &port.sort.sort, &names);
                }
            }
            scope.push(&operation.name, Dependent(true));
        }
        for (law, member) in members.laws.iter().zip(&written.faces) {
            let form = forms.next();
            let stated = match form {
                Some(&Ok(ModelForm::Law {
                    ref telescope,
                    ref carrier,
                    ref left,
                    ref right,
                })) => Some((telescope, carrier, left, right)),
                Some(_) | None => None,
            };
            let base = scope.binders.len();
            let mut binders: &[Binder] = &[];
            if let Some((telescope, carrier, left, right)) = stated {
                let tail = Tail::Path(carrier, left, right);
                let codomain = Codomain::Path(carrier, left, right);
                if let Some(ty) = self.telescope(&mut scope, telescope, tail, codomain)
                    && let Maybe::Present(named) = member.named
                {
                    let context = self.context(&scope);
                    self.emit(named, DescribedRole::Name, ty, context);
                }
                for (binder, binds) in telescope.iter().zip(dependence(telescope, tail)) {
                    scope.push(&binder.name, binds);
                }
                binders = telescope;
            }
            let sides = [
                (&law.left, &member.left, stated.map(|stated| stated.2)),
                (&law.right, &member.right, stated.map(|stated| stated.3)),
            ];
            for (side, nodes, elaborated) in sides {
                self.law_side(
                    &scope,
                    binders,
                    &operations,
                    &heads,
                    side,
                    nodes,
                    elaborated,
                );
            }
            scope.binders.truncate(base);
        }
        for member in &written.circuits {
            self.circuit(&scope, &members, member, &heads);
        }
    }

    /// Record each node of a law's side `side`, written as `nodes`, under
    /// `scope`: a variable at its binder's sort among `telescope`, an
    /// application at its operation's result over the arguments `elaborated`
    /// gives it, and an application's head at its operation's type.
    ///
    /// # Specification
    /// - requires: `elaborated`, when present, is `side` with each
    ///   application's implicit arguments inserted.
    /// - ensures: as the summary states, each node at the bytes `nodes` holds
    ///   for it.
    /// - fails: never; a node no sort is minted for records nothing.
    /// - panics: none.
    /// - executable: none — as [`Self::sign`].
    ///
    /// # Termination
    /// Each node of the finite side is popped once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp(id(a), f)` answers at `Hom(a, b)`, `id(a)` at
    ///   `Hom(a, a)`, `a` at `Ob` and `comp` at its type.
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    #[expect(
        clippy::too_many_arguments,
        reason = "the scope, the law's binders, the operations' forms and types, the side, its nodes and its elaboration are each read"
    )]
    fn law_side(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        operations: &BTreeMap<Name, (&[Binder], &[SortTerm])>,
        heads: &BTreeMap<Name, (ValueTypeId, ContextIndex)>,
        side: &FreeTerm,
        nodes: &WrittenTerm,
        elaborated: Option<&FreeTerm>,
    )
    {
        let context = self.context(scope);
        let mut pending: Vec<(TermNode<'_>, Option<TermNode<'_>>)> =
            Vec::from([(side.to_node(), elaborated.map(FreeTerm::to_node))]);
        let mut at = nodes.nodes.iter();
        while let Some((node, image)) = pending.pop() {
            let Some(written) = at.next()
            else {
                break;
            };
            match node.view() {
                TermView::Var(name) => {
                    if let Some(binder) = telescope.iter().rev().find(|binder| binder.name == *name)
                        && let Some(ty) = self.sort(scope, &binder.sort)
                    {
                        self.emit(written.span, DescribedRole::Term, ty, context);
                    }
                },
                TermView::Op { name, args } => {
                    if let (Maybe::Present(head), Some(&(ty, stated))) =
                        (written.head, heads.get(name))
                    {
                        self.emit(head, DescribedRole::Term, ty, stated);
                    }
                    let args: Vec<TermNode<'_>> = args.collect();
                    let images: Vec<TermNode<'_>> = match image.map(TermNode::view) {
                        Some(TermView::Op { args, .. }) => args.collect(),
                        Some(_) | None => Vec::new(),
                    };
                    let single =
                        operations
                            .get(name)
                            .and_then(|&(binders, results)| match *results {
                                [ref result] => Some((binders, result)),
                                _ => None,
                            });
                    if let (Some((binders, result)), false) = (single, images.is_empty()) {
                        let owned: Vec<FreeTerm> =
                            images.iter().map(|image| image.to_term()).collect();
                        let by: BTreeMap<&Name, &FreeTerm> = binders
                            .iter()
                            .map(|binder| &binder.name)
                            .zip(&owned)
                            .collect();
                        let sort = SortTerm {
                            sort: result.sort.clone(),
                            indices: result
                                .indices
                                .iter()
                                .map(|index| substitute(index, &by))
                                .collect(),
                        };
                        if let Some(ty) = self.sort(scope, &sort) {
                            self.emit(written.span, DescribedRole::Term, ty, context);
                        }
                    }
                    let implicit = images.len().saturating_sub(args.len());
                    for (place, arg) in args.into_iter().enumerate().rev() {
                        let image = images.get(place.saturating_add(implicit)).copied();
                        pending.push((arg, image));
                    }
                },
                TermView::Ctor { args, .. } | TermView::Results { args } => {
                    let first = pending.len();
                    pending.extend(args.map(|arg| (arg, None)));
                    if let Some(added) = pending.get_mut(first ..) {
                        added.reverse();
                    }
                },
            }
        }
    }

    /// Record a circuit rule's ports, rewrite sides and wires at the sort
    /// each meets, and each node line's operation head at its type, under
    /// `scope`, every sort and operation of the sign.
    ///
    /// # Specification
    /// - requires: `scope` binds the sign's sorts and operations.
    /// - ensures: a wire's sort is the first its ports, its rewrite port or an
    ///   operation's port it meets give it, where that sort is one the sign
    ///   declares unindexed; each name written at a sorted wire answers at that
    ///   sort.
    /// - fails: never; a wire no sort reaches records nothing.
    /// - panics: none.
    /// - executable: none — as [`Self::sign`].
    ///
    /// # Termination
    /// Each round over the node lines sorts a wire or stops, and there are
    /// finitely many wires.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `cong1`'s wires `x`, `x′`, `y` and `z` answer at
    ///   `Nat`, and `add` at its type.
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    fn circuit(
        &mut self,
        scope: &Scope,
        members: &Members,
        circuit: &WrittenCircuit,
        heads: &BTreeMap<Name, (ValueTypeId, ContextIndex)>,
    )
    {
        let declared = |sort: &Name| {
            members
                .sorts
                .iter()
                .any(|held| held.name == *sort && held.indices.is_empty())
        };
        let names: Vec<Name> = members.sorts.iter().map(|sort| sort.name.clone()).collect();
        let mut wires: BTreeMap<Name, Name> = BTreeMap::new();
        for port in &circuit.ports {
            if declared(&port.sort) {
                let _first = wires.insert(port.name.clone(), port.sort.clone());
            }
        }
        let mut rewrites: BTreeMap<Name, (&Name, &Name)> = BTreeMap::new();
        for rewrite in &circuit.rewrites {
            let _first = rewrites.insert(
                rewrite.named.name.clone(),
                (&rewrite.left.name, &rewrite.right.name),
            );
        }
        for _round in 0 ..= circuit.frames.len().saturating_add(circuit.rewrites.len()) {
            let before = wires.len();
            for &(left, right) in rewrites.values() {
                let shared = wires.get(left).or_else(|| wires.get(right)).cloned();
                if let Some(sort) = shared {
                    for side in [left, right] {
                        if !declared(side) {
                            let _held = wires.entry(side.clone()).or_insert_with(|| sort.clone());
                        }
                    }
                }
            }
            for frame in &circuit.frames {
                let reads: Vec<Option<Name>> =
                    if let Some(&(left, right)) = rewrites.get(&frame.head.name) {
                        let sort = if declared(left) {
                            Some(left.clone())
                        }
                        else {
                            wires
                                .get(left)
                                .or_else(|| wires.get(right))
                                .cloned()
                                .or_else(|| {
                                    frame
                                        .arguments
                                        .iter()
                                        .chain(&frame.outputs)
                                        .find_map(|wire| wires.get(&wire.name).cloned())
                                })
                        };
                        frame
                            .arguments
                            .iter()
                            .chain(&frame.outputs)
                            .map(|_| sort.clone())
                            .collect()
                    }
                    else if let Some(operation) = members
                        .operations
                        .iter()
                        .find(|operation| operation.name == frame.head.name)
                    {
                        operation
                            .inputs
                            .iter()
                            .chain(&operation.outputs)
                            .map(|port| {
                                (port.sort.indices.is_empty() && declared(&port.sort.sort))
                                    .then(|| port.sort.sort.clone())
                            })
                            .collect()
                    }
                    else {
                        Vec::new()
                    };
                for (wire, sort) in frame.arguments.iter().chain(&frame.outputs).zip(reads) {
                    if let Some(sort) = sort {
                        let _held = wires.entry(wire.name.clone()).or_insert(sort);
                    }
                }
            }
            if wires.len() == before {
                break;
            }
        }
        let context = self.context(scope);
        let wire = |typer: &mut Self, name: &Name, span: ByteSpan, role: DescribedRole| {
            if let Some(sort) = wires.get(name) {
                let term = SortTerm {
                    sort: sort.clone(),
                    indices: Vec::new(),
                };
                if let Some(ty) = typer.sort(scope, &term) {
                    typer.emit(span, role, ty, context);
                }
            }
        };
        for port in &circuit.ports {
            if let Maybe::Present(named) = port.written.named {
                wire(self, &port.name, named, DescribedRole::Name);
            }
            self.occurrence(&port.written.sort, &port.sort, &names);
        }
        for rewrite in &circuit.rewrites {
            for side in [&rewrite.left, &rewrite.right] {
                if declared(&side.name) {
                    self.occurrence(
                        &WrittenSort {
                            span: side.span,
                            indices: Vec::new(),
                        },
                        &side.name,
                        &names,
                    );
                }
                else {
                    wire(self, &side.name, side.span, DescribedRole::Term);
                }
            }
        }
        for frame in &circuit.frames {
            if let Some(&(ty, stated)) = heads.get(&frame.head.name) {
                self.emit(frame.head.span, DescribedRole::Term, ty, stated);
            }
            for written in frame.arguments.iter().chain(&frame.outputs) {
                wire(self, &written.name, written.span, DescribedRole::Term);
            }
        }
    }

    /// Record every constructor, operation and rule of the unparameterised
    /// `data` family `description`, written as `written`, over `families`,
    /// the type and universe of each family the module declares, and
    /// `constructors`, each constructor's fields and family.
    ///
    /// # Specification
    /// - requires: `written` is where the family's reader read its
    ///   constructors, operations and rules.
    /// - ensures: as the module documentation states for a data family.
    /// - fails: never; a port whose sort names no family records nothing, nor
    ///   does an operation with such a port.
    /// - panics: none.
    /// - executable: none — as [`Self::sign`].
    ///
    /// # Termination
    /// Each node of each finite rule side is popped once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `divmod`, `walk` and their rules answer at their
    ///   types and sorts.
    /// - witness: `described::tests::a_data_rule_answers_each_node_at_its_sort`
    fn family(
        &mut self,
        description: &SignDesc<DescriptionGrade>,
        written: &WrittenMembers,
        families: &BTreeMap<Name, (ValueTypeId, ValueTypeId)>,
        constructors: &BTreeMap<Name, (Vec<ValueTypeId>, ValueTypeId)>,
    )
    {
        let closed = self.context(&Scope::default());
        // A field's type is minted by the family's admission, apart from the
        // family's own: the two are read as equal when they say the same.
        let universe_of = |arena: &CoreArena, ty: ValueTypeId| {
            families
                .values()
                .find(|&&(held, _)| held == ty || arena.value_type(held) == arena.value_type(ty))
                .map(|&(_, universe)| universe)
        };
        for (constructor, member) in description.ctors.iter().zip(&written.constructors) {
            let Some(&(ref fields, family)) = constructors.get(&constructor.name)
            else {
                continue;
            };
            let ty = if fields.is_empty() {
                family
            }
            else {
                let mut chain = self.arena.comp_type_returner(family);
                for &field in fields.iter().rev() {
                    chain = self.arena.comp_type_arrow(field, chain);
                }
                self.arena.value_type_thunk(chain)
            };
            self.emit(member.named, DescribedRole::Name, ty, closed);
            for (&field, port) in fields.iter().zip(&member.fields) {
                if let Maybe::Present(named) = port.named {
                    self.emit(named, DescribedRole::Name, field, closed);
                }
                if let Some(universe) = universe_of(self.arena, field) {
                    self.emit(port.sort.span, DescribedRole::Type, universe, closed);
                }
            }
            if let Some(universe) = universe_of(self.arena, family) {
                self.emit(member.result, DescribedRole::Type, universe, closed);
            }
        }
        let mut operations: BTreeMap<Name, Operation> = BTreeMap::new();
        for (operation, member) in description.opers.iter().zip(&written.operations) {
            let ports = operation
                .arity
                .inputs
                .iter()
                .zip(&member.inputs)
                .chain(operation.arity.outputs.iter().zip(&member.outputs));
            for (port, at) in ports {
                if let Some(&(ty, universe)) = families.get(&port.sort) {
                    if let Maybe::Present(named) = at.named {
                        self.emit(named, DescribedRole::Name, ty, closed);
                    }
                    self.emit(at.sort.span, DescribedRole::Type, universe, closed);
                }
            }
            let sorted = |ports: &[gandr_theory_levitation::SortRef]| -> Option<Vec<ValueTypeId>> {
                ports
                    .iter()
                    .map(|port| families.get(&port.sort).map(|&(ty, _)| ty))
                    .collect()
            };
            let (Some(inputs), Some(outputs)) = (
                sorted(&operation.arity.inputs),
                sorted(&operation.arity.outputs),
            )
            else {
                continue;
            };
            let result = match *outputs.as_slice() {
                [one] => one,
                _ => self.arena.value_type_product(&outputs),
            };
            let mut chain = self.arena.comp_type_returner(result);
            for &input in inputs.iter().rev() {
                chain = self.arena.comp_type_arrow(input, chain);
            }
            let ty = self.arena.value_type_thunk(chain);
            self.emit(member.named, DescribedRole::Name, ty, closed);
            let _first =
                operations.insert(operation.name.clone(), Operation { inputs, result, ty });
        }
        for (face, member) in description.rules.iter().zip(&written.faces) {
            let mut variables: BTreeMap<&Name, ValueTypeId> = BTreeMap::new();
            let mut unsorted: Vec<(ByteSpan, Name)> = Vec::new();
            let root = match face.lhs.view() {
                TermView::Op { name, .. } => operations.get(name).map(|operation| operation.result),
                TermView::Var(_) | TermView::Ctor { .. } | TermView::Results { .. } => None,
            };
            for (side, nodes, expected) in [
                (&face.lhs, &member.left, None),
                (&face.rhs, &member.right, root),
            ] {
                let mut pending = Vec::from([(side.to_node(), expected)]);
                let mut at = nodes.nodes.iter();
                while let Some((node, expected)) = pending.pop() {
                    let Some(written) = at.next()
                    else {
                        break;
                    };
                    let (ty, below): (
                        Option<ValueTypeId>,
                        Vec<(TermNode<'_>, Option<ValueTypeId>)>,
                    ) = match node.view() {
                        TermView::Var(name) => {
                            let ty = variables.get(name).copied().or(expected);
                            if let Some(ty) = ty {
                                let _held = variables.entry(name).or_insert(ty);
                            }
                            else {
                                unsorted.push((written.span, name.clone()));
                            }
                            (ty, Vec::new())
                        },
                        TermView::Op { name, args } => {
                            let operation = operations.get(name);
                            if let (Maybe::Present(head), Some(operation)) =
                                (written.head, operation)
                            {
                                self.emit(head, DescribedRole::Term, operation.ty, closed);
                            }
                            let below = args
                                .enumerate()
                                .map(|(place, arg)| {
                                    (
                                        arg,
                                        operation.and_then(|operation| {
                                            operation.inputs.get(place).copied()
                                        }),
                                    )
                                })
                                .collect();
                            (operation.map(|operation| operation.result), below)
                        },
                        TermView::Ctor { name, args } => {
                            let constructor = constructors.get(name);
                            let below = args
                                .enumerate()
                                .map(|(place, arg)| {
                                    (arg, constructor.and_then(|held| held.0.get(place).copied()))
                                })
                                .collect();
                            (constructor.map(|&(_, family)| family), below)
                        },
                        TermView::Results { args } => {
                            let components: Vec<ValueTypeId> = match expected
                                .and_then(|expected| self.arena.value_type(expected))
                            {
                                Some(&ValueType::Product(ref components)) => components.to_vec(),
                                Some(_) | None => Vec::new(),
                            };
                            let below = args
                                .enumerate()
                                .map(|(place, arg)| (arg, components.get(place).copied()))
                                .collect();
                            (expected.filter(|_| !components.is_empty()), below)
                        },
                    };
                    if let Some(ty) = ty {
                        self.emit(written.span, DescribedRole::Term, ty, closed);
                    }
                    pending.extend(below.into_iter().rev());
                }
            }
            for (span, name) in unsorted {
                if let Some(&ty) = variables.get(&name) {
                    self.emit(span, DescribedRole::Term, ty, closed);
                }
            }
        }
    }

    /// Record every constructor of the parameterised `data` family
    /// `constant`, whose parameters are `parameters` and whose signature is
    /// `signature`, written as `written`.
    ///
    /// # Specification
    /// - requires: `written` is where the family's reader read its
    ///   constructors, in the order `signature` lists them.
    /// - ensures: under the parameters, a constant constructor's name answers
    ///   at the family applied to them, one with fields at `+U (A₁ -> … -> -F
    ///   F(…))`, each field's name at its type; the written result at the
    ///   family's universe, and each of its arguments naming a parameter at
    ///   that parameter's classifier.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::sign`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Maybe(a)`'s constructors, fields, result and its
    ///   argument answer under `a`.
    /// - witness: `described::tests::a_parameterised_constructor_answers_under_its_parameters`
    fn parameterised(
        &mut self,
        parameters: &[FamilyParameter],
        written: &WrittenMembers,
        constant: ConstantIndex,
        signature: &DataSignature,
    )
    {
        let mut scope = Scope::default();
        for parameter in parameters {
            scope.push(&parameter.name, Dependent(true));
        }
        let context = self.context(&scope);
        let count = signature.parameters().len();
        let mut arguments = Vec::with_capacity(count);
        for index in (0 .. count).rev() {
            let index = DeBruijnIndex::from(u32::try_from(index).unwrap_or(u32::MAX));
            arguments.push(self.arena.value_variable(Zone::Intuitionistic, index));
        }
        let family = self.arena.value_type_data(constant, arguments);
        let mut classifiers = Vec::with_capacity(count);
        for (place, &classifier) in signature.parameters().iter().enumerate() {
            let lift = u32::try_from(count.saturating_sub(place)).unwrap_or(u32::MAX);
            classifiers.push(gandr_core_term::shift_value_type(
                self.arena,
                classifier,
                Binders::from(lift),
            ));
        }
        for (fields, member) in signature.constructors().iter().zip(&written.constructors) {
            let ty = if fields.is_empty() {
                family
            }
            else {
                let mut chain = self.arena.comp_type_returner(family);
                for &field in fields.iter().rev() {
                    chain = self.arena.comp_type_arrow(field, chain);
                }
                self.arena.value_type_thunk(chain)
            };
            self.emit(member.named, DescribedRole::Name, ty, context);
            for (&field, port) in fields.iter().zip(&member.fields) {
                if let Maybe::Present(named) = port.named {
                    self.emit(named, DescribedRole::Name, field, context);
                }
            }
            self.emit(
                member.result,
                DescribedRole::Type,
                signature.kind(),
                context,
            );
            for (&argument, &classifier) in member.arguments.iter().zip(&classifiers) {
                self.emit(argument, DescribedRole::Type, classifier, context);
            }
        }
    }
}

impl LoweredModule<'_>
{
    /// The type each described node answers at, minted into `arena`.
    ///
    /// # Specification
    /// - requires: `arena` is the one the module was lowered into.
    /// - ensures: for every `sign` block and every unparameterised `data`
    ///   family's operations and rules, each written node at the type its
    ///   member states, as the [`crate::described`] documentation lays out,
    ///   each read in its context; the first context is the empty one.
    /// - provides: what a face answers inside a described declaration.
    /// - fails: never; a node no type is stated for records nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sign's sorts, operations, laws and circuit and a
    ///   data family's operations and rules answer at the types asserted.
    /// - witness: `described::tests::a_sign_answers_at_every_member`
    /// - witness: `described::tests::a_data_rule_answers_each_node_at_its_sort`
    #[spec(ensures: |ret| ret.contexts.first().is_some_and(Vec::is_empty)
        && ret.entries.iter().all(|entry| usize::from(entry.context) < ret.contexts.len()))]
    #[inline]
    pub fn described_types(
        &self,
        arena: &mut CoreArena,
    ) -> DescribedTypes
    {
        let mut typer = Typer {
            arena,
            types: DescribedTypes {
                entries: Vec::new(),
                contexts: Vec::from([Vec::new()]),
            },
        };
        let mut families: BTreeMap<Name, (ValueTypeId, ValueTypeId)> = BTreeMap::new();
        let mut constructors: BTreeMap<Name, (Vec<ValueTypeId>, ValueTypeId)> = BTreeMap::new();
        let mut parameterised: BTreeMap<Name, (ConstantIndex, &DataSignature)> = BTreeMap::new();
        let base = typer.universe(Level::zero());
        for (name, atom) in [("Integer", BaseType::Integer), ("String", BaseType::String)] {
            let ty = typer.arena.value_type_base(atom);
            let _first = families.insert(Name::from(name), (ty, base));
        }
        let unit = typer.arena.value_type_unit();
        let _first = families.insert(Name::from("Unit"), (unit, base));
        for declaration in self.declarations() {
            // The words of a family's loops are minted under the family's
            // name, never written: the name is the family's.
            if declaration.role() == crate::module::Role::Words {
                continue;
            }
            let DeclarationOutcome::Data(index) = declaration.outcome()
            else {
                continue;
            };
            let Maybe::Present(signature) = self.data(index)
            else {
                continue;
            };
            if !signature.parameters().is_empty() {
                let _first = parameterised.insert(
                    Name::from(declaration.name().as_ref()),
                    (declaration.constant(), signature),
                );
                continue;
            }
            let ty = typer
                .arena
                .value_type_data(declaration.constant(), Vec::new());
            let _first = families.insert(
                Name::from(declaration.name().as_ref()),
                (ty, signature.kind()),
            );
            for (name, fields) in self
                .constructors(index)
                .iter()
                .zip(signature.constructors())
            {
                let _first = constructors.insert(Name::from(name.as_str()), (fields.clone(), ty));
            }
        }
        for described in &self.descriptions().declarations {
            match described.presentation {
                Maybe::Present(ref presentation) => {
                    typer.sign(presentation, &described.written);
                },
                Maybe::Absent(_) => {
                    if described.description.polarity != DeclPolarity::Data {
                        continue;
                    }
                    if described.parameters.is_empty() {
                        typer.family(
                            &described.description,
                            &described.written,
                            &families,
                            &constructors,
                        );
                    }
                    else if let Some(&(constant, signature)) =
                        parameterised.get(&described.description.id.name)
                    {
                        typer.parameterised(
                            &described.parameters,
                            &described.written,
                            constant,
                            signature,
                        );
                    }
                },
            }
        }
        typer.types
    }
}

#[cfg(test)]
mod tests;
