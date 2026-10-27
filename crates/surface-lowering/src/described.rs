//! The types a described declaration's members state, each at the node the
//! source writes it at, for a face answering a reader who points there.
//!
//! # A member answers at what it states
//!
//! A `theory` block, and a `data` family's constructors and its `oper` and
//! `rule` members, write no term the typed run judges: the description route
//! reads them ([`crate::description`]). It states their types here, in the core
//! vocabulary every face spells through, at the bytes
//! [`crate::description::written`] keeps for each node:
//!
//! - **A theory** reads as the telescope `Model(S)` lays its components out in
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
//!   where that sort is one the theory declares unindexed. A stated law's name
//!   answers at the type its component states, into the `Path` it concludes;
//!   its statement and each path at their universe; each binder at its sort and
//!   each hypothesis's name at the path it assumes; each node of a side as a
//!   rule's, a `true` or `false` at the path's carrier. A port that binds a
//!   variable (`t : pi+ (x : S) . T`) answers at the thunked function from its
//!   variables, `+U ((x : S) -> -F T)`, as its operation's component takes it,
//!   and each binder's name at its sort. A law relating a term at such a port
//!   has no component: a field `bind x .` names its variable at the sort the
//!   port binds it at, and each occurrence of that variable, an instantiation's
//!   argument among them, answers there. An operation whose index applies a
//!   binding port, `Below(k(x), l(x))`, has no component either: its ports read
//!   as written, `k(x)` at `k`'s sort and `x` at the sort its port binds.
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
//!   naming a parameter at that parameter's classifier. A family the native
//!   reading owns whole ([`crate::description::NativeFamily`]) reads the same
//!   way, at its native signature, with or without parameters.
//! - **A codata family's** observations read under its parameters: each node of
//!   an observation's type at its universe — the family itself at its kind, a
//!   parameter read as a type at the universe its code is read out of — and
//!   each argument naming a parameter at that parameter's classifier.
//!
//! A component the derivation cannot state answers nowhere, and neither does
//! a node no position sorts.
//!
//! - Choice: read a theory as a telescope of variables, its sorts codes in
//!   `Type`, so each member answers at the type `Model(S)` derives, spelled by
//!   the names the theory writes. Alternatives: a nominal atom per sort, which
//!   the core keeps for sealed abstract types alone and no constant of the
//!   module names; and the presentation spelled as text, which bypasses the
//!   printer every face shares. Reversal: a theory's `Model(S)` components
//!   lowered to core declarations of their own — beside the value `S : Theory`
//!   the block already defines — which a face then reads as it reads any other.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CodataSignature;
use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use quenchant_shape::shape::Maybe;

use crate::DeclarationOutcome;
use crate::description::DescriptionGrade;
use crate::description::FamilyParameter;
use crate::description::written::WrittenCircuit;
use crate::description::written::WrittenMembers;
use crate::description::written::WrittenOperation;
use crate::description::written::WrittenPath;
use crate::description::written::WrittenPort;
use crate::description::written::WrittenSort;
use crate::description::written::WrittenTerm;
use crate::lower::atom_type;
use crate::model::Binder;
use crate::model::BuiltinSort;
use crate::model::Dependent;
use crate::model::Members;
use crate::model::ModelFault;
use crate::model::ModelForm;
use crate::model::Port;
use crate::model::Presentation;
use crate::model::PresentedOperation;
use crate::model::SortTerm;
use crate::model::Tail;
use crate::model::Variable;
use crate::model::dependence;
use crate::model::derive_members;
use crate::model::variable_dependence;
use crate::module::LoweredModule;
use crate::resolve::SurfaceName;
use crate::resolve::type_atom;

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

/// A written use of a theory's sort or operation, beside the name tile the
/// member is declared by.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DescribedUse
{
    /// The bytes the use names the member by.
    pub span: ByteSpan,
    /// The member's own name tile.
    pub named: ByteSpan,
}

/// Every described node's type, the contexts they are read in, and each
/// theory member's written uses.
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
    /// Each written use of a theory's sort or operation: a written sort's
    /// head, and an operation applied in a law or an index term.
    pub uses: Vec<DescribedUse>,
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
    /// The universe of the ground sort a sort's family lands in: a sort's
    /// kind.
    Universe(GroundSort),
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
    /// An instantiation of the metavariable named over this many terms last
    /// rebuilt.
    Inst(&'term Name, usize),
    /// An abstraction of the atom whose body has been rebuilt.
    Abs(&'term Name),
    /// A binding field whose body has been rebuilt.
    Lam(&'term Name),
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

/// What a theory's members declare for the nodes after them: its sorts' names,
/// and each operation the derivation states with its telescope, its results
/// and its type.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Declared<'form>
{
    /// The sorts' names, in written order.
    sorts: Vec<Name>,
    /// Each stated operation's telescope and results.
    operations: BTreeMap<Name, (&'form [Binder], &'form [SortTerm])>,
    /// Each stated operation's type, with the context it is stated in.
    heads: BTreeMap<Name, (ValueTypeId, ContextIndex)>,
}

/// How a law's side is read: over the arguments its `Model(S)` component's
/// elaboration gives each application, or, for a law no component states,
/// at the sorts the theory writes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Reading<'law, 'form>
{
    /// The side as the component elaborates it, when it states one.
    Elaborated(Option<&'form FreeTerm>),
    /// The sorts the theory writes for a law no component states.
    Written(&'law Unstated<'form>),
}

/// A path a stated law writes, `Path(C, l, r)`: its carrier and its two sides.
///
/// # Specification
/// trivial.
type PathParts<'term> = (&'term SortTerm, &'term FreeTerm, &'term FreeTerm);

/// The sorts a law no `Model(S)` component states reads its nodes at, as the
/// theory writes them: each operation by name, each variable its left side
/// places at a first-order port, or under a field for each variable a binding
/// port binds, at that port's sort, and each variable a binding port binds
/// at the sort of the term it stands for, under the port's binders.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Unstated<'form>
{
    /// Each operation the theory declares, by name.
    operations: &'form BTreeMap<&'form Name, &'form PresentedOperation>,
    /// Each first-order variable of the left side, at its port's sort.
    variables: BTreeMap<&'form Name, &'form SortTerm>,
    /// Each variable a binding port binds, written there under fewer fields
    /// than the port binds, at the port's sort.
    bound: BTreeMap<&'form Name, &'form SortTerm>,
}

impl<'form> Unstated<'form>
{
    /// The sorts the left side `left` gives its variables, each at the port
    /// of `operations` it fills.
    ///
    /// # Specification
    /// - ensures: each variable an application of a declared operation holds
    ///   directly, or under the abstractions and fields of a binding port, at
    ///   the sort of the port it fills: among `variables` for a first-order
    ///   port or one whose every variable a field over it binds, among `bound`
    ///   for a binding port it stands at under fewer fields than that; a
    ///   variable no application holds so is in neither.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the placement is read off the side's nodes, which a
    ///   predicate would walk again.
    ///
    /// # Termination
    /// Each node of the finite side is popped once, and each application's
    /// finite arguments are read once, each abstraction's body once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `let(u, t)` places `u` at `Tm` and `t` at the binding
    ///   port's `Tm`; `nu(bind a . p)` places `p` at the abstracting port's
    ///   `Proc`; `new(bind x . q)` places `q` at the field's `C`.
    /// - witness: `described::tests::a_second_order_law_answers_at_its_written_sorts`
    /// - witness: `described::tests::a_variable_under_an_abstraction_answers_at_its_port`
    /// - witness: `described::tests::a_field_s_variable_and_an_instantiation_under_it_answer_2360`
    fn of(
        operations: &'form BTreeMap<&'form Name, &'form PresentedOperation>,
        left: &'form FreeTerm,
    ) -> Self
    {
        let mut variables = BTreeMap::new();
        let mut bound = BTreeMap::new();
        let mut pending = Vec::from([left.to_node()]);
        while let Some(node) = pending.pop() {
            match node.view() {
                TermView::Var(_) | TermView::Atom(_) | TermView::Bound(_) => {},
                TermView::Op { name, args } => {
                    if let Some(operation) = operations.get(name) {
                        for (arg, port) in args.clone().zip(&operation.inputs) {
                            // The fields written over the argument: a variable
                            // under one per variable the port binds is a term of
                            // the port's sort, one under fewer the port's own.
                            let mut held = arg;
                            let mut fields = 0_usize;
                            loop {
                                let (body, field) = match held.view() {
                                    TermView::Abs { mut args, .. } => (args.next(), false),
                                    TermView::Lam { mut args, .. } => (args.next(), true),
                                    TermView::Var(_)
                                    | TermView::Ctor { .. }
                                    | TermView::Op { .. }
                                    | TermView::Results { .. }
                                    | TermView::Inst { .. }
                                    | TermView::Atom(_)
                                    | TermView::Bound(_) => break,
                                };
                                let Some(body) = body
                                else {
                                    break;
                                };
                                fields = fields.saturating_add(usize::from(field));
                                held = body;
                            }
                            if let TermView::Var(variable) = held.view() {
                                let into = if fields >= port.binders.len() {
                                    &mut variables
                                }
                                else {
                                    &mut bound
                                };
                                let _first = into.insert(variable, &port.sort);
                            }
                        }
                    }
                    pending.extend(args);
                },
                TermView::Ctor { args, .. }
                | TermView::Results { args }
                | TermView::Inst { args, .. }
                | TermView::Abs { args, .. }
                | TermView::Lam { args, .. } => pending.extend(args),
            }
        }
        Self {
            operations,
            variables,
            bound,
        }
    }

    /// The sort an application of `operation` stands at, when it has one
    /// output of an unindexed sort.
    ///
    /// # Specification
    /// - ensures: the output's sort for a declared operation of one output
    ///   whose sort has no indices; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `let(u, t)` stands at `Tm`.
    /// - witness: `described::tests::a_second_order_law_answers_at_its_written_sorts`
    #[spec(ensures: |ret| ret.is_none_or(|sort| sort.indices.is_empty()))]
    fn result(
        &self,
        operation: &Name,
    ) -> Option<&'form SortTerm>
    {
        match *self.operations.get(operation)?.outputs.as_slice() {
            [ref one] if one.sort.indices.is_empty() => Some(&one.sort),
            _ => None,
        }
    }
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
    /// The name tile of each sort and operation of the theory being read, by
    /// name; empty outside a theory.
    members: BTreeMap<Name, ByteSpan>,
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
/// - witness: `described::tests::a_theory_answers_at_every_member`
#[spec(ensures: |ret| !by.is_empty() || ret.eq(term))]
fn substitute(
    term: &FreeTerm,
    by: &BTreeMap<&Name, FreeTerm>,
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
                        .map_or_else(|| FreeTerm::var(name.clone()), Clone::clone),
                ),
                TermView::Atom(name) => built.push(FreeTerm::atom(name.clone())),
                TermView::Bound(name) => built.push(FreeTerm::bound(name.clone())),
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
                TermView::Inst { name, args } => {
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Rebuild::Inst(name, args.len()));
                    pending.extend(args.into_iter().rev().map(Rebuild::Read));
                },
                TermView::Abs { atom, args } => {
                    pending.push(Rebuild::Abs(atom));
                    pending.extend(args.map(Rebuild::Read));
                },
                TermView::Lam { var, args } => {
                    pending.push(Rebuild::Lam(var));
                    pending.extend(args.map(Rebuild::Read));
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
            Rebuild::Inst(name, count) => {
                let args = take(&mut built, count);
                built.push(FreeTerm::inst(name.clone(), args));
            },
            Rebuild::Abs(atom) => {
                let body = built.pop().unwrap_or_else(|| FreeTerm::results([]));
                built.push(FreeTerm::abs(atom.clone(), body));
            },
            Rebuild::Lam(var) => {
                let body = built.pop().unwrap_or_else(|| FreeTerm::results([]));
                built.push(FreeTerm::lam(var.clone(), body));
            },
        }
    }
    built.pop().unwrap_or_else(|| term.clone())
}

/// What a node of a written observation type is read as.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy)]
enum Observed
{
    /// A type, which answers at its universe.
    Type(ValueTypeId),
    /// An argument: a parameter, or the code of a type.
    Value(ValueId),
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

    /// Record `span` as a use of the theory member `name`, when the theory
    /// being read declares one.
    ///
    /// # Specification
    /// trivial.
    fn refer(
        &mut self,
        span: ByteSpan,
        name: &Name,
    )
    {
        if let Some(&named) = self.members.get(name) {
            self.types.uses.push(DescribedUse { span, named });
        }
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
    /// variable `g` names, and a law's `true` or `false` its injection into
    /// `Bool`; none for any other constructor, a results tuple or a name the
    /// scope does not bind.
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
                    TermView::Ctor { name, ref args }
                        if matches!(name.as_ref(), "true" | "false")
                            && args.clone().next().is_none() =>
                    {
                        let side = if name.as_ref() == "true" {
                            gandr_kernel_term::Side::Left
                        }
                        else {
                            gandr_kernel_term::Side::Right
                        };
                        let unit = self.arena.value_unit();
                        built.push(
                            self.arena
                                .value_injection(gandr_kernel_term::Summand::from(side), unit),
                        );
                    },
                    TermView::Ctor { .. }
                    | TermView::Results { .. }
                    | TermView::Inst { .. }
                    | TermView::Abs { .. }
                    | TermView::Atom(_)
                    | TermView::Lam { .. }
                    | TermView::Bound(_) => {
                        return None;
                    },
                },
                Step::Apply(name, count) => {
                    let start = built.len().checked_sub(count)?;
                    let applied = self.apply(scope, name, built.get(start ..)?)?;
                    built.truncate(start);
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
    /// sort's code, applied to its indices' values, or the host universe a bare
    /// `Type` or the builtin type an unindexed name no binder of `scope`
    /// answers names.
    ///
    /// # Specification
    /// trivial.
    fn sort(
        &mut self,
        scope: &Scope,
        sort: &SortTerm,
    ) -> Option<ValueTypeId>
    {
        let builtin = sort.builtin();
        if let Maybe::Present(BuiltinSort::Universe(ground)) = builtin {
            return Some(
                self.arena
                    .value_type_universe(Sort::Ground(ground), Level::zero()),
            );
        }
        let code = if sort.indices.is_empty() {
            let Some(index) = scope.variable(&sort.sort)
            else {
                return match builtin {
                    Maybe::Present(BuiltinSort::Atom(atom)) => Some(atom_type(self.arena, atom)),
                    Maybe::Present(BuiltinSort::Universe(_)) | Maybe::Absent(_) => None,
                };
            };
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
    /// - witness: `described::tests::a_theory_answers_at_every_member`
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
            domains.push(self.domain(scope, binder)?);
            scope.push(&binder.name, binds);
        }
        let result = match codomain {
            Codomain::Universe(ground) => self
                .arena
                .value_type_universe(Sort::Ground(ground), Level::zero()),
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
            Codomain::Path(carrier, left, right) => self.path(scope, (carrier, left, right))?,
        };
        Some(self.quantified(&domains, dependent, result))
    }

    /// The thunk of the returner of `result` under each of `domains`, innermost
    /// last: a Π for a domain `dependent` marks as binding and an arrow for any
    /// other.
    ///
    /// # Specification
    /// trivial.
    fn quantified(
        &mut self,
        domains: &[ValueTypeId],
        dependent: &[Dependent],
        result: ValueTypeId,
    ) -> ValueTypeId
    {
        let mut chain = self.arena.comp_type_returner(result);
        for (&domain, binds) in domains.iter().zip(dependent).rev() {
            chain = if binds.0 {
                self.arena.comp_type_pi(domain, chain)
            }
            else {
                self.arena.comp_type_arrow(domain, chain)
            };
        }
        self.arena.value_type_thunk(chain)
    }

    /// The type `binder` binds under `scope`: its sort's type, or for a
    /// binder that takes variables the thunked function from them to it.
    ///
    /// # Specification
    /// trivial.
    #[spec(captures: before = scope.binders.len(), ensures: scope.binders.len() == before)]
    fn domain(
        &mut self,
        scope: &mut Scope,
        binder: &Binder,
    ) -> Option<ValueTypeId>
    {
        if binder.over.is_empty() {
            return self.sort(scope, &binder.sort);
        }
        let dependent = variable_dependence(&binder.over, &binder.sort);
        let base = scope.binders.len();
        let minted = self.taken(scope, binder, &dependent);
        scope.binders.truncate(base);
        minted
    }

    /// The body of [`Self::domain`] for a binder that takes variables, leaving
    /// the variables it pushes on `scope`.
    ///
    /// # Specification
    /// trivial.
    fn taken(
        &mut self,
        scope: &mut Scope,
        binder: &Binder,
        dependent: &[Dependent],
    ) -> Option<ValueTypeId>
    {
        let mut domains = Vec::with_capacity(binder.over.len());
        for (variable, &binds) in binder.over.iter().zip(dependent) {
            domains.push(self.sort(scope, &variable.sort)?);
            scope.push(&variable.name, binds);
        }
        let result = self.sort(scope, &binder.sort)?;
        Some(self.quantified(&domains, dependent, result))
    }

    /// Record a written sort at the universe its sorts are coded in, when its
    /// head is one of `sorts` or a builtin type, or at the universe above the
    /// host's types when it is `Type`, an index over the host's types.
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
        let builtin = matches!(
            type_atom(SurfaceName::from(head.as_ref())),
            Maybe::Present(_)
        );
        let closed = self.context(&Scope::default());
        if sorts.contains(head) || builtin {
            let universe = self.universe(Level::zero());
            self.emit(written.span, DescribedRole::Type, universe, closed);
        }
        else if head.as_ref() == crate::form::TileName::UNIVERSE.as_ref()
            && let Ok(level) = Level::zero().succ()
        {
            let universe = self.universe(level);
            self.emit(written.span, DescribedRole::Type, universe, closed);
        }
        // The head is the sort's name, written first: `M`, or `Hom` in
        // `Hom(a, b)`.
        let start = written.span.start();
        let end = usize::from(start)
            .saturating_add(head.as_ref().len())
            .min(usize::from(written.span.end()));
        if let Ok(named) = ByteSpan::new(start, ByteOffset::from(end)) {
            self.refer(named, head);
        }
    }

    /// Record each node of a written sort's index terms, `raw` as written and
    /// `elaborated` as the derivation reads it, under `scope`, as
    /// [`Self::law_side`] records a law's side: a variable at its binder's
    /// sort among `telescope`, an application at its operation's result and
    /// its head at the operation's type.
    ///
    /// # Specification
    /// trivial.
    fn indices(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        declared: &Declared<'_>,
        raw: &SortTerm,
        elaborated: &SortTerm,
        written: &WrittenSort,
    )
    {
        let terms = raw.indices.iter().zip(&elaborated.indices);
        for ((term, image), nodes) in terms.zip(&written.indices) {
            self.law_side(
                scope,
                telescope,
                declared,
                term,
                nodes,
                Reading::Elaborated(Some(image)),
            );
        }
    }

    /// Record each port of `ports`, written as `written` and presented as
    /// `raws`, the last binders of `telescope` — those before them are
    /// inserted — its name at the type its binder binds under the binders
    /// before it, its sort at its universe, and its sort's index terms; a
    /// binding port as [`Self::taking`] records it.
    ///
    /// # Specification
    /// trivial.
    fn ports(
        &mut self,
        scope: &mut Scope,
        telescope: &[Binder],
        dependent: &[Dependent],
        raws: &[Port],
        written: &[WrittenPort],
        declared: &Declared<'_>,
    )
    {
        let first = telescope.len().saturating_sub(written.len());
        let base = scope.binders.len();
        for (at, (binder, &binds)) in telescope.iter().zip(dependent).enumerate() {
            if let Some(place) = at.checked_sub(first)
                && let (Some(port), Some(raw)) = (written.get(place), raws.get(place))
            {
                if binder.over.is_empty() {
                    self.port(scope, telescope, declared, &raw.sort, &binder.sort, port);
                }
                else {
                    self.taking(scope, telescope, declared, raw, binder, port);
                }
            }
            scope.push(&binder.name, binds);
        }
        scope.binders.truncate(base);
    }

    /// Record one binding port, presented as `raw`, derived as `binder` and
    /// written as `port`, under `scope`: its name at the thunked function its
    /// binder binds, each variable's name at its sort under the variables
    /// before it, and its sort under all of them, each sort at its universe
    /// with its index terms.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `get`'s continuation answers at the function from its
    ///   state, its variable at the state's sort, so a binding port read as
    ///   first-order, or its variable unread, shows.
    /// - witness: `described::tests::a_binding_port_answers_at_the_function_from_its_variables_765`
    #[spec(captures: before = scope.binders.len(), ensures: scope.binders.len() == before)]
    fn taking(
        &mut self,
        scope: &mut Scope,
        telescope: &[Binder],
        declared: &Declared<'_>,
        raw: &Port,
        binder: &Binder,
        port: &WrittenPort,
    )
    {
        if let Maybe::Present(named) = port.named
            && let Some(ty) = self.domain(scope, binder)
        {
            let context = self.context(scope);
            self.emit(named, DescribedRole::Name, ty, context);
        }
        let dependent = variable_dependence(&binder.over, &binder.sort);
        let base = scope.binders.len();
        let variables = binder
            .over
            .iter()
            .zip(&raw.binders)
            .zip(&port.binders)
            .zip(&dependent);
        for (((variable, presented), at), &binds) in variables {
            if let Some(ty) = self.sort(scope, &variable.sort) {
                let context = self.context(scope);
                self.emit(at.named, DescribedRole::Name, ty, context);
            }
            self.occurrence(&at.sort, &variable.sort.sort, &declared.sorts);
            self.indices(
                scope,
                telescope,
                declared,
                &presented.sort,
                &variable.sort,
                &at.sort,
            );
            scope.push(&variable.name, binds);
        }
        self.occurrence(&port.sort, &binder.sort.sort, &declared.sorts);
        self.indices(
            scope,
            telescope,
            declared,
            &raw.sort,
            &binder.sort,
            &port.sort,
        );
        scope.binders.truncate(base);
    }

    /// Record one port of sort `sort`, presented as `raw` and written as
    /// `port`, under `scope`.
    ///
    /// # Specification
    /// trivial.
    fn port(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        declared: &Declared<'_>,
        raw: &SortTerm,
        sort: &SortTerm,
        port: &WrittenPort,
    )
    {
        if let Maybe::Present(named) = port.named
            && let Some(ty) = self.sort(scope, sort)
        {
            let context = self.context(scope);
            self.emit(named, DescribedRole::Name, ty, context);
        }
        self.occurrence(&port.sort, &sort.sort, &declared.sorts);
        self.indices(scope, telescope, declared, raw, sort, &port.sort);
    }

    /// The path type `Path(C, l, r)` under `scope`, from its carrier and its
    /// two sides as the derivation elaborates them.
    ///
    /// # Specification
    /// trivial.
    fn path(
        &mut self,
        scope: &Scope,
        (carrier, left, right): PathParts<'_>,
    ) -> Option<ValueTypeId>
    {
        let over = self.sort(scope, carrier)?;
        let from = self.value(scope, left)?;
        let to = self.value(scope, right)?;
        Some(self.arena.value_type_path(over, from, to))
    }

    /// Record a path a stated law assumes or concludes, presented as `raw`,
    /// elaborated as `elaborated` and written as `written`, under `scope`,
    /// the law's binders among `telescope`: the path at its universe, its
    /// carrier at its own, and each side as [`Self::law_side`] records one, a
    /// `true` or `false` at the carrier. The path's type, when it mints.
    ///
    /// # Specification
    /// trivial.
    fn stated_path(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        declared: &Declared<'_>,
        raw: PathParts<'_>,
        elaborated: PathParts<'_>,
        written: &WrittenPath,
    ) -> Option<ValueTypeId>
    {
        let context = self.context(scope);
        let universe = self.universe(Level::zero());
        self.emit(written.span, DescribedRole::Type, universe, context);
        let (carrier, left, right) = elaborated;
        self.occurrence(&written.carrier, &carrier.sort, &declared.sorts);
        self.indices(scope, telescope, declared, raw.0, carrier, &written.carrier);
        let sides = [(raw.1, left, &written.left), (raw.2, right, &written.right)];
        for (side, image, nodes) in sides {
            let literal = matches!(
                side.to_node().view(),
                TermView::Ctor { name, .. } if matches!(name.as_ref(), "true" | "false")
            );
            if !literal {
                self.law_side(
                    scope,
                    telescope,
                    declared,
                    side,
                    nodes,
                    Reading::Elaborated(Some(image)),
                );
            }
            else if let (Some(leaf), Some(ty)) = (nodes.nodes.first(), self.sort(scope, carrier))
            {
                self.emit(leaf.span, DescribedRole::Term, ty, context);
            }
        }
        self.path(scope, elaborated)
    }

    /// Record the ports of `operation`, written as `member`, under `scope`,
    /// when `Model(S)` states no component for it: one of its ports abstracts
    /// an atom, or an index applies a binding port, `Below(k(x), l(x))`. Its
    /// name answers nowhere; its ports read as the written telescope states
    /// them, each under every port before it, a binding port taking its
    /// variables.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an operation whose index applies a binding port
    ///   answers at each binder's sort and each index term, so an operation
    ///   read only for its sorts' heads shows.
    /// - witness: `described::tests::an_unelaborated_operation_s_ports_answer_as_written_2969`
    fn binding(
        &mut self,
        scope: &mut Scope,
        operation: &PresentedOperation,
        member: &WrittenOperation,
        declared: &Declared<'_>,
    )
    {
        let telescope: Vec<Binder> = operation
            .inputs
            .iter()
            .map(|port| Binder {
                name: port.name.clone(),
                over: port
                    .binders
                    .iter()
                    .map(|variable| Variable {
                        name: variable.name.clone(),
                        sort: variable.sort.clone(),
                    })
                    .collect(),
                sort: port.sort.clone(),
            })
            .collect();
        let base = scope.binders.len();
        for (port, written) in operation.inputs.iter().zip(&member.inputs) {
            self.bound(scope, &telescope, port, written, declared);
            scope.push(&port.name, Dependent(true));
        }
        for (port, written) in operation.outputs.iter().zip(&member.outputs) {
            self.bound(scope, &telescope, port, written, declared);
        }
        scope.binders.truncate(base);
    }

    /// Record one port `port` of an abstracting operation, written as
    /// `written`, under `scope`: a first-order port as [`Self::port`] does; a
    /// bound or abstracting port's atoms and binders each at its sort, their
    /// sorts and its own at their universe, and their index terms, its own
    /// sort's under the variables it binds. Such a port's name answers
    /// nowhere: no core type states a `bind` port. No derivation elaborates
    /// these sorts, so each is read as written.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `bind` port beside first-order ones: its atom
    ///   answers at its atom sort and its own name nowhere, so an abstracting
    ///   port read as first-order, or not read at all, shows.
    /// - witness: `described::tests::a_variable_under_an_abstraction_answers_at_its_port`
    /// - witness: `described::tests::an_unelaborated_operation_s_ports_answer_as_written_2969`
    fn bound(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        port: &Port,
        written: &WrittenPort,
        declared: &Declared<'_>,
    )
    {
        if port.binders.is_empty() && port.abstractions.is_empty() {
            self.port(scope, telescope, declared, &port.sort, &port.sort, written);
            return;
        }
        let binders = port.abstractions.iter().chain(&port.binders);
        for (binder, at) in binders.zip(&written.binders) {
            if let Some(ty) = self.sort(scope, &binder.sort) {
                let context = self.context(scope);
                self.emit(at.named, DescribedRole::Name, ty, context);
            }
            self.occurrence(&at.sort, &binder.sort.sort, &declared.sorts);
            self.indices(
                scope,
                telescope,
                declared,
                &binder.sort,
                &binder.sort,
                &at.sort,
            );
        }
        // The port's own sort reads under the variables it binds: `x` in
        // `q : pi+ (x : V) . Below(k(x), l(x))` is `q`'s.
        let under: Vec<Binder> = telescope.iter().chain(&port.binders).cloned().collect();
        self.occurrence(&written.sort, &port.sort.sort, &declared.sorts);
        self.indices(
            scope,
            &under,
            declared,
            &port.sort,
            &port.sort,
            &written.sort,
        );
    }

    /// Record every member of a theory presenting `presentation`, written as
    /// `written`, the theories it nests models of read at `code`, the type
    /// `Theory` the module mints, when it mints one.
    ///
    /// # Specification
    /// - requires: `written` is where the theory reader read `presentation`'s
    ///   members.
    /// - ensures: as the module documentation states for a theory: each sort,
    ///   operation, rule and stated law at what its `Model(S)` component
    ///   states, each port and each stated law's binder at its sort, each
    ///   hypothesis at the path it assumes, each node of a rule or a stated law
    ///   at its sort, each node of a rule a `derive` declaration states over
    ///   the theory at the sort the theory writes for it, each written sort,
    ///   statement and path at its universe, each circuit's ports and wires at
    ///   their sorts, a nested model's `Model(T)` at its universe and its `T`
    ///   at `code`; and each written sort's head and each operation applied,
    ///   beside the name tile of the member it names.
    /// - fails: never; a presentation whose members cannot be read records
    ///   nothing, and a component the derivation cannot state records none of
    ///   the nodes its type would read, save an abstracting operation's ports,
    ///   which read as written.
    /// - panics: none.
    /// - executable: none — each node answers at a type minted into the arena,
    ///   which no predicate over the presentation restates; the witness reads
    ///   each back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the probe theories' sorts, operations, rules, stated
    ///   laws and circuit answer at the types asserted; the identity-return
    ///   `lam`'s binder answers at its indexed sort and its port at the
    ///   function from it.
    /// - witness: `described::tests::a_theory_answers_at_every_member`
    /// - witness: `described::tests::a_stated_law_answers_at_its_statement_2356`
    /// - witness: `described::tests::a_derived_rule_answers_each_side_node_at_its_sort`
    /// - witness: `described::tests::a_binding_port_answers_at_the_function_from_its_variables_765`
    /// - witness: `description::theory::tests::a_model_type_reads_as_a_nested_model_1226`
    fn theory(
        &mut self,
        presentation: &Presentation,
        written: &WrittenMembers,
        code: Option<ValueTypeId>,
    )
    {
        let Ok(members) = presentation.members()
        else {
            return;
        };
        let model = derive_members(&members, &presentation.circuits, &presentation.laws);
        self.members = members
            .sorts
            .iter()
            .map(|sort| (sort.name.clone(), sort.named.span))
            .chain(
                members
                    .operations
                    .iter()
                    .zip(&written.operations)
                    .filter_map(|(operation, member)| match member.named {
                        Maybe::Present(named) => Some((operation.name.clone(), named)),
                        Maybe::Absent(_) => None,
                    }),
            )
            .collect();
        self.types
            .uses
            .extend(written.uses.iter().map(|used| DescribedUse {
                span: used.span,
                named: used.named,
            }));
        let mut declared = Declared {
            sorts: members.sorts.iter().map(|sort| sort.name.clone()).collect(),
            operations: BTreeMap::new(),
            heads: BTreeMap::new(),
        };
        let mut scope = Scope::default();
        let mut forms = model.components.iter().map(|component| &component.form);
        let closed = self.context(&Scope::default());
        for (sort, member) in members.sorts.iter().zip(&written.sorts) {
            if let Ok(level) = Level::zero().succ() {
                let universe = self.universe(level);
                self.emit(member.classifier, DescribedRole::Type, universe, closed);
            }
            if let Some(&Ok(ModelForm::Sort {
                ref indices,
                ground,
            })) = forms.next()
            {
                let tail = Tail::Results(&[]);
                let kind = if indices.is_empty() {
                    Some(
                        self.arena
                            .value_type_universe(Sort::Ground(ground), Level::zero()),
                    )
                }
                else {
                    self.telescope(&mut scope, indices, tail, Codomain::Universe(ground))
                };
                if let Some(kind) = kind {
                    let context = self.context(&scope);
                    self.emit(member.named, DescribedRole::Name, kind, context);
                }
                let dependent = dependence(indices, tail);
                self.ports(
                    &mut scope,
                    indices,
                    &dependent,
                    &sort.indices,
                    &member.indices,
                    &declared,
                );
            }
            scope.push(&sort.name, Dependent(true));
        }
        for (operation, member) in members.operations.iter().zip(&written.operations) {
            for &(span, ground) in &member.formers {
                let universe = self
                    .arena
                    .value_type_universe(Sort::Ground(ground), Level::zero());
                let closed = self.context(&Scope::default());
                self.emit(span, DescribedRole::Type, universe, closed);
            }
            let form = forms.next();
            if let Some(&Ok(ModelForm::Operation {
                ref telescope,
                ref results,
            })) = form
            {
                let tail = Tail::Results(results);
                if let Some(ty) =
                    self.telescope(&mut scope, telescope, tail, Codomain::Results(results))
                {
                    let context = self.context(&scope);
                    if let Maybe::Present(named) = member.named {
                        self.emit(named, DescribedRole::Name, ty, context);
                    }
                    let _first = declared.heads.insert(operation.name.clone(), (ty, context));
                }
                let _first = declared
                    .operations
                    .insert(operation.name.clone(), (telescope, results));
                let dependent = dependence(telescope, tail);
                self.ports(
                    &mut scope,
                    telescope,
                    &dependent,
                    &operation.inputs,
                    &member.inputs,
                    &declared,
                );
                let base = scope.binders.len();
                for (binder, &binds) in telescope.iter().zip(&dependent) {
                    scope.push(&binder.name, binds);
                }
                let outputs = results.iter().zip(&operation.outputs);
                for ((result, raw), port) in outputs.zip(&member.outputs) {
                    self.port(&scope, telescope, &declared, &raw.sort, result, port);
                }
                scope.binders.truncate(base);
            }
            else if let Some(&Ok(ModelForm::Constant(ref sort))) = form {
                if let Some(ty) = self.sort(&scope, sort) {
                    let context = self.context(&scope);
                    if let Maybe::Present(named) = member.named {
                        self.emit(named, DescribedRole::Name, ty, context);
                    }
                    let _first = declared.heads.insert(operation.name.clone(), (ty, context));
                }
                let _first = declared
                    .operations
                    .insert(operation.name.clone(), (&[], core::slice::from_ref(sort)));
                let outputs = operation.outputs.iter().zip(&member.outputs);
                for (raw, port) in outputs {
                    self.port(&scope, &[], &declared, &raw.sort, sort, port);
                }
            }
            else if matches!(
                form,
                Some(&Err(ModelFault::Abstraction
                    | ModelFault::Binding
                    | ModelFault::UnknownHead))
            ) {
                self.binding(&mut scope, operation, member, &declared);
            }
            else if let Some(&Ok(ModelForm::Nested(_))) = form {
                if let (Some(code), Some(port)) = (code, member.outputs.first()) {
                    self.emit(port.sort.span, DescribedRole::Term, code, closed);
                }
            }
            else {
                let presented = operation.inputs.iter().chain(&operation.outputs);
                for (port, at) in presented.zip(member.inputs.iter().chain(&member.outputs)) {
                    self.occurrence(&at.sort, &port.sort.sort, &declared.sorts);
                }
            }
            scope.push(&operation.name, Dependent(true));
        }
        let presented: BTreeMap<&Name, &PresentedOperation> = members
            .operations
            .iter()
            .map(|operation| (&operation.name, operation))
            .collect();
        for (law, member) in members.laws.iter().zip(&written.faces) {
            let form = forms.next();
            let stated = match form {
                Some(&Ok(ModelForm::Law {
                    ref telescope,
                    ref hypotheses,
                    ref carrier,
                    ref left,
                    ref right,
                })) => Some((telescope, carrier, left, right, hypotheses)),
                Some(_) | None => None,
            };
            let base = scope.binders.len();
            let mut binders: &[Binder] = &[];
            if let Some((telescope, carrier, left, right, hypotheses)) = stated {
                let tail = Tail::Path(hypotheses, carrier, left, right);
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
            // A law no component states, one relating a term at a binding
            // port, reads its nodes at the sorts the theory writes.
            let unstated = stated
                .is_none()
                .then(|| Unstated::of(&presented, &law.left));
            let sides = [
                (&law.left, &member.left, stated.map(|stated| stated.2)),
                (&law.right, &member.right, stated.map(|stated| stated.3)),
            ];
            for (side, nodes, elaborated) in sides {
                let read = unstated
                    .as_ref()
                    .map_or(Reading::Elaborated(elaborated), Reading::Written);
                self.law_side(&scope, binders, &declared, side, nodes, read);
            }
            scope.binders.truncate(base);
        }
        // A stated law: its statement at its universe, its name at the type
        // its component states, each written binder as an operation's port,
        // each hypothesis's name at the path it assumes, and each path it
        // assumes or concludes as `stated_path` records it.
        for (law, member) in presentation.laws.iter().zip(&written.laws) {
            let Some(&Ok(ModelForm::Law {
                ref telescope,
                ref hypotheses,
                ref carrier,
                ref left,
                ref right,
            })) = forms.next()
            else {
                continue;
            };
            let universe = self.universe(Level::zero());
            let context = self.context(&scope);
            self.emit(member.statement, DescribedRole::Type, universe, context);
            let tail = Tail::Path(hypotheses, carrier, left, right);
            let codomain = Codomain::Path(carrier, left, right);
            if let Some(ty) = self.telescope(&mut scope, telescope, tail, codomain) {
                self.emit(member.named, DescribedRole::Name, ty, context);
            }
            let base = scope.binders.len();
            // The written binders are the telescope's last: those before them
            // are the sort variables the derivation inserts.
            let first = telescope.len().saturating_sub(member.binders.len());
            for (at, (binder, binds)) in telescope
                .iter()
                .zip(dependence(telescope, tail))
                .enumerate()
            {
                if let Some(place) = at.checked_sub(first)
                    && let (Some(port), Some(raw)) =
                        (member.binders.get(place), law.binders.get(place))
                {
                    self.port(&scope, telescope, &declared, &raw.sort, &binder.sort, port);
                }
                scope.push(&binder.name, binds);
            }
            let assumed = law
                .hypotheses
                .iter()
                .zip(hypotheses)
                .zip(&member.hypotheses);
            for ((raw, elaborated), &(named, ref path)) in assumed {
                let raw = (&raw.carrier, &raw.left, &raw.right);
                let elaborated = (&elaborated.carrier, &elaborated.left, &elaborated.right);
                if let Some(ty) =
                    self.stated_path(&scope, telescope, &declared, raw, elaborated, path)
                {
                    let context = self.context(&scope);
                    self.emit(named, DescribedRole::Name, ty, context);
                }
            }
            let raw = (&law.carrier, &law.left, &law.right);
            let _concluded = self.stated_path(
                &scope,
                telescope,
                &declared,
                raw,
                (carrier, left, right),
                &member.path,
            );
            scope.binders.truncate(base);
        }
        // A rule a `derive` declaration states is a law no component states:
        // its nodes read at the sorts the theory writes.
        for derived in &written.derived {
            let unstated = Unstated::of(&presented, &derived.left.0);
            for &(ref side, ref nodes) in [&derived.left, &derived.right] {
                self.law_side(
                    &scope,
                    &[],
                    &declared,
                    side,
                    nodes,
                    Reading::Written(&unstated),
                );
            }
        }
        for member in &written.circuits {
            self.circuit(&scope, &members, member, &declared.heads);
        }
        self.members.clear();
    }

    /// Record each node of a law's side `side`, written as `nodes`, under
    /// `scope`, as `read` reads it: a variable at its binder's sort among
    /// `telescope`, an application at its operation's result over the
    /// arguments the elaboration gives it, and an application's head at its
    /// operation's type; for a law no component states, a variable and an
    /// application at the unindexed sort the theory writes for them, an
    /// instantiation at the sort of its variable's binding port or else of
    /// the port it stands at, an abstraction's atom at the atom sort its port
    /// abstracts there, a field's variable at the representable sort its port
    /// binds there, and an atom's or a field variable's occurrence at the sort
    /// of the port it stands at or else of its binder. A binding port of
    /// `telescope` applied to as many terms as it takes variables, `k(x)` in a
    /// sort read as written, answers at the port's sort, its head at the
    /// function the port binds.
    ///
    /// # Specification
    /// - requires: an elaboration, when present, is `side` with each
    ///   application's implicit arguments inserted.
    /// - ensures: as the summary states, each node at the bytes `nodes` holds
    ///   for it; a variable a binding port binds, written there under fewer
    ///   fields than the port binds, answers nowhere, and an abstraction
    ///   nowhere, as its port does.
    /// - fails: never; a node no sort is minted for records nothing.
    /// - panics: none.
    /// - executable: none — as [`Self::theory`].
    ///
    /// # Termination
    /// Each node of the finite side is popped once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp(id(a), f)` answers at `Hom(a, b)`, `id(a)` at
    ///   `Hom(a, a)`, `a` at `Ob`, `comp` at its type and the variable `f` at
    ///   the code its sort returns; the identity-return signature's index
    ///   `arrow(a, b)` at `CTy`; `let(u, t)`, `u` and `t(u)` at `Tm`; the atom
    ///   of `bind a . p` at `Name`; `a` in `out(a, nil())` at `Name`; `k(d, c)`
    ///   under `bind d .` and `bind c .` at the port's `C`, and `d` and `c`
    ///   there at the sorts their ports bind them at; `k(x)` in `mono`'s index
    ///   at `k`'s sort `C`, and `k` at the function from `V`.
    /// - witness: `described::tests::a_theory_answers_at_every_member`
    /// - witness: `described::tests::a_binding_port_answers_at_the_function_from_its_variables_765`
    /// - witness: `described::tests::a_second_order_law_answers_at_its_written_sorts`
    /// - witness: `described::tests::a_variable_under_an_abstraction_answers_at_its_port`
    /// - witness: `described::tests::an_occurrence_answers_at_its_port`
    /// - witness: `described::tests::an_unelaborated_operation_s_ports_answer_as_written_2969`
    /// - witness: `described::tests::a_field_s_variable_and_an_instantiation_under_it_answer_2360`
    fn law_side(
        &mut self,
        scope: &Scope,
        telescope: &[Binder],
        declared: &Declared<'_>,
        side: &FreeTerm,
        nodes: &WrittenTerm,
        read: Reading<'_, '_>,
    )
    {
        // Each node with its elaboration, the atoms its port abstracts and the
        // variables it binds that no abstraction or field above it has taken,
        // the port's sort, and the innermost entry of the variables bound
        // above it, one past its index among `scoped`.
        type Pending<'term> = (
            TermNode<'term>,
            Option<TermNode<'term>>,
            &'term [Binder],
            &'term [Binder],
            Option<&'term SortTerm>,
            usize,
        );
        let (elaborated, unstated) = match read {
            Reading::Elaborated(elaborated) => (elaborated, None),
            Reading::Written(unstated) => (None, Some(unstated)),
        };
        let context = self.context(scope);
        let mut pending: Vec<Pending<'_>> = Vec::from([(
            side.to_node(),
            elaborated.map(FreeTerm::to_node),
            &[][..],
            &[][..],
            None,
            0_usize,
        )]);
        // Each atom an abstraction binds and each variable a field binds, at
        // its sort, beside the entry of the one bound above it.
        let mut scoped: Vec<(usize, &Name, &SortTerm)> = Vec::new();
        let mut at = nodes.nodes.iter();
        // The elaborated arguments by the binder each instantiates, refilled
        // per application.
        let mut by: BTreeMap<&Name, FreeTerm> = BTreeMap::new();
        while let Some((node, image, atoms, fields, port, innermost)) = pending.pop() {
            let Some(written) = at.next()
            else {
                break;
            };
            match node.view() {
                TermView::Var(name) => {
                    let sort = telescope
                        .iter()
                        .rev()
                        .find(|binder| binder.name == *name)
                        .map(|binder| &binder.sort)
                        .or_else(|| {
                            unstated
                                .and_then(|unstated| unstated.variables.get(name).copied())
                                .filter(|sort| sort.indices.is_empty())
                        });
                    if let Some(sort) = sort
                        && let Some(ty) = self.sort(scope, sort)
                    {
                        self.emit(written.span, DescribedRole::Term, ty, context);
                    }
                },
                TermView::Atom(name) | TermView::Bound(name) => {
                    // Else the sort its innermost binder of that name gives it.
                    let mut above = innermost;
                    let mut binding = None;
                    while let Some(&(outer, bound, sort)) =
                        above.checked_sub(1).and_then(|at| scoped.get(at))
                    {
                        if bound == name {
                            binding = Some(sort);
                            break;
                        }
                        above = outer;
                    }
                    let sort = port.or_else(|| binding.filter(|sort| sort.indices.is_empty()));
                    if let Some(sort) = sort
                        && let Some(ty) = self.sort(scope, sort)
                    {
                        self.emit(written.span, DescribedRole::Name, ty, context);
                    }
                },
                TermView::Op { name, args } => {
                    if let (Maybe::Present(head), Some(&(ty, stated))) =
                        (written.head, declared.heads.get(name))
                    {
                        self.emit(head, DescribedRole::Term, ty, stated);
                    }
                    if let Maybe::Present(head) = written.head {
                        self.refer(head, name);
                    }
                    let args: Vec<TermNode<'_>> = args.collect();
                    // The elaboration's arguments, when it reads the node as
                    // an application: none for a constant, `pt()`, which still
                    // answers at its sort (#668).
                    let images: Option<Vec<TermNode<'_>>> = match image.map(TermNode::view) {
                        Some(TermView::Op { args, .. }) => Some(args.collect()),
                        Some(_) | None => None,
                    };
                    let single = declared
                        .operations
                        .get(name)
                        .and_then(|&(binders, results)| match *results {
                            [ref result] => Some((binders, result)),
                            _ => None,
                        });
                    // A side read as written supplies no implicit argument: its
                    // node answers only where the operation binds none.
                    if let (Some((binders, result)), Some(images)) = (single, images.as_deref())
                        && binders.len() == images.len()
                    {
                        by.clear();
                        by.extend(
                            binders
                                .iter()
                                .map(|binder| &binder.name)
                                .zip(images.iter().map(|image| image.to_term())),
                        );
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
                    else if let Some(sort) = unstated.and_then(|unstated| unstated.result(name))
                        && let Some(ty) = self.sort(scope, sort)
                    {
                        self.emit(written.span, DescribedRole::Term, ty, context);
                    }
                    // A binding port applied to its variables, `k(x)` in a sort
                    // read as written: the call at the port's sort, its head at
                    // the function the port binds, minted where its sort names
                    // none of its variables.
                    else if let Some(taken) =
                        telescope.iter().rev().find(|binder| binder.name == *name)
                        && !taken.over.is_empty()
                        && taken.over.len() == args.len()
                        && let Some(result) = self.sort(scope, &taken.sort)
                    {
                        self.emit(written.span, DescribedRole::Term, result, context);
                        let dependent = variable_dependence(&taken.over, &taken.sort);
                        let domains: Option<Vec<ValueTypeId>> = taken
                            .over
                            .iter()
                            .map(|variable| self.sort(scope, &variable.sort))
                            .collect();
                        if let Maybe::Present(head) = written.head
                            && dependent.iter().all(|binds| !binds.0)
                            && let Some(domains) = domains
                        {
                            let ty = self.quantified(&domains, &dependent, result);
                            self.emit(head, DescribedRole::Term, ty, context);
                        }
                    }
                    let images = images.unwrap_or_default();
                    let implicit = images.len().saturating_sub(args.len());
                    let ports = unstated
                        .and_then(|unstated| unstated.operations.get(name))
                        .map_or(&[][..], |operation| operation.inputs.as_slice());
                    for (place, arg) in args.into_iter().enumerate().rev() {
                        let image = images.get(place.saturating_add(implicit)).copied();
                        let port = ports.get(place);
                        let (atoms, fields) = port.map_or((&[][..], &[][..]), |port| {
                            (port.abstractions.as_slice(), port.binders.as_slice())
                        });
                        pending.push((
                            arg,
                            image,
                            atoms,
                            fields,
                            port.map(|port| &port.sort),
                            innermost,
                        ));
                    }
                },
                TermView::Inst { name, args } => {
                    if let Some(sort) = unstated
                        .and_then(|unstated| unstated.bound.get(name).copied())
                        .or(port)
                        .filter(|sort| sort.indices.is_empty())
                        && let Some(ty) = self.sort(scope, sort)
                    {
                        self.emit(written.span, DescribedRole::Term, ty, context);
                    }
                    let first = pending.len();
                    pending.extend(args.map(|arg| (arg, None, &[][..], &[][..], None, innermost)));
                    if let Some(added) = pending.get_mut(first ..) {
                        added.reverse();
                    }
                },
                TermView::Abs {
                    atom: bound,
                    mut args,
                }
                | TermView::Lam {
                    var: bound,
                    mut args,
                } => {
                    // An abstraction takes the next atom its port abstracts, a
                    // field the next variable its port binds.
                    let field = matches!(node.view(), TermView::Lam { .. });
                    let taken = if field { fields } else { atoms };
                    let (inner, below) = taken
                        .split_first()
                        .map_or((None, taken), |(inner, below)| (Some(inner), below));
                    if let (Maybe::Present(binder), Some(inner)) = (written.head, inner)
                        && let Some(ty) = self.sort(scope, &inner.sort)
                    {
                        self.emit(binder, DescribedRole::Name, ty, context);
                    }
                    let innermost = inner.map_or(innermost, |inner| {
                        scoped.push((innermost, bound, &inner.sort));
                        scoped.len()
                    });
                    let (atoms, fields) = if field {
                        (atoms, below)
                    }
                    else {
                        (below, fields)
                    };
                    if let Some(body) = args.next() {
                        pending.push((body, None, atoms, fields, port, innermost));
                    }
                },
                TermView::Ctor { args, .. } | TermView::Results { args } => {
                    let first = pending.len();
                    pending.extend(args.map(|arg| (arg, None, &[][..], &[][..], None, innermost)));
                    if let Some(added) = pending.get_mut(first ..) {
                        added.reverse();
                    }
                },
            }
        }
    }

    /// Record a circuit rule's ports, rewrite sides and wires at the sort
    /// each meets, and each node line's operation head at its type, under
    /// `scope`, every sort and operation of the theory.
    ///
    /// # Specification
    /// - requires: `scope` binds the theory's sorts and operations.
    /// - ensures: a wire's sort is the first its ports, its rewrite port or an
    ///   operation's port it meets give it, where that sort is one the theory
    ///   declares unindexed; each name written at a sorted wire answers at that
    ///   sort.
    /// - fails: never; a wire no sort reaches records nothing.
    /// - panics: none.
    /// - executable: none — as [`Self::theory`].
    ///
    /// # Termination
    /// Each round over the node lines sorts a wire or stops, and there are
    /// finitely many wires.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `cong1`'s wires `x`, `x′`, `y` and `z` answer at
    ///   `Nat`, and `add` at its type; a wire only a later reading reaches, a
    ///   rewrite side read off the side it rewrites and an output read off its
    ///   operation's result each answer at their sort.
    /// - witness: `described::tests::a_theory_answers_at_every_member`
    /// - witness: `described::tests::a_circuit_wire_takes_its_sort_from_whichever_reading_reaches_it`
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
        let mut operations = BTreeMap::new();
        for operation in &members.operations {
            let _first = operations.entry(&operation.name).or_insert(operation);
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
                    else if let Some(operation) = operations.get(&frame.head.name) {
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
    /// `constructors`, each constructor's fields, family and tag.
    ///
    /// # Specification
    /// - requires: `written` is where the family's reader read its
    ///   constructors, operations and rules.
    /// - ensures: as the module documentation states for a data family.
    /// - fails: never; a port whose sort names no family, or applies one to a
    ///   term that is no constructor term, records nothing, nor does an
    ///   operation with such a port.
    /// - panics: none.
    /// - executable: none — as [`Self::theory`].
    ///
    /// # Termination
    /// Each node of each finite rule side is popped once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `divmod`, `walk`, `half` and their rules answer at
    ///   their types and sorts, a field's sort at its family's universe and a
    ///   one-result operation's result at the family itself; an indexed
    ///   family's operation and rule answer at the family at the index its
    ///   ports write.
    /// - witness: `described::tests::a_data_rule_answers_each_node_at_its_sort`
    /// - witness: `described::tests::an_indexed_family_s_operation_answers_at_its_index_2940`
    fn family(
        &mut self,
        description: &TheoryDesc<DescriptionGrade>,
        written: &WrittenMembers,
        families: &BTreeMap<Name, (ValueTypeId, ValueTypeId)>,
        constructors: &BTreeMap<Name, (Vec<ValueTypeId>, ValueTypeId, ConstructorTag)>,
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
            let Some(&(ref fields, family, _)) = constructors.get(&constructor.name)
            else {
                continue;
            };
            let ty = if fields.is_empty() {
                family
            }
            else {
                gandr_core_term::constructor_classifier(self.arena, family, fields)
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
                if let Some((ty, universe)) = self.port_family(port, families, constructors) {
                    if let Maybe::Present(named) = at.named {
                        self.emit(named, DescribedRole::Name, ty, closed);
                    }
                    self.emit(at.sort.span, DescribedRole::Type, universe, closed);
                    self.index_nodes(port, &at.sort, constructors, closed);
                }
            }
            let sorted = |typer: &mut Self, ports: &[SortRef]| -> Option<Vec<ValueTypeId>> {
                ports
                    .iter()
                    .map(|port| {
                        typer
                            .port_family(port, families, constructors)
                            .map(|(ty, _)| ty)
                    })
                    .collect()
            };
            let (Some(inputs), Some(outputs)) = (
                sorted(self, &operation.arity.inputs),
                sorted(self, &operation.arity.outputs),
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
            if let Maybe::Present(named) = member.named {
                self.emit(named, DescribedRole::Name, ty, closed);
            }
            let _first =
                operations.insert(operation.name.clone(), Operation { inputs, result, ty });
        }
        for (face, member) in description.rules.iter().zip(&written.faces) {
            let mut variables: BTreeMap<&Name, ValueTypeId> = BTreeMap::new();
            let mut unsorted: Vec<(ByteSpan, Name)> = Vec::new();
            let root = match face.lhs.view() {
                TermView::Op { name, .. } => operations.get(name).map(|operation| operation.result),
                TermView::Var(_)
                | TermView::Ctor { .. }
                | TermView::Results { .. }
                | TermView::Inst { .. }
                | TermView::Abs { .. }
                | TermView::Atom(_)
                | TermView::Lam { .. }
                | TermView::Bound(_) => None,
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
                            (constructor.map(|&(_, family, _)| family), below)
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
                        TermView::Inst { args, .. } => {
                            (expected, args.map(|arg| (arg, None)).collect())
                        },
                        TermView::Abs { args, .. } | TermView::Lam { args, .. } => {
                            (None, args.map(|arg| (arg, None)).collect())
                        },
                        TermView::Atom(_) | TermView::Bound(_) => (expected, Vec::new()),
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

    /// The type and universe of the family the sort of `port` names among
    /// `families`: the family itself over no terms, and over index terms the
    /// family at the values they denote, as [`Self::constructed`] reads them.
    ///
    /// # Specification
    /// trivial.
    fn port_family(
        &mut self,
        port: &SortRef,
        families: &BTreeMap<Name, (ValueTypeId, ValueTypeId)>,
        constructors: &BTreeMap<Name, (Vec<ValueTypeId>, ValueTypeId, ConstructorTag)>,
    ) -> Option<(ValueTypeId, ValueTypeId)>
    {
        let &(ty, universe) = families.get(&port.sort)?;
        if port.arguments.is_empty() {
            return Some((ty, universe));
        }
        let Some(&ValueType::Data { declaration, .. }) = self.arena.value_type(ty)
        else {
            return None;
        };
        let mut indices = Vec::with_capacity(port.arguments.len());
        for term in &port.arguments {
            indices.push(self.constructed(term, constructors)?);
        }
        Some((self.arena.value_type_data(declaration, indices), universe))
    }

    /// The value the constructor term `term` denotes over `constructors`:
    /// each constructor applied to as many terms as it has fields; none for
    /// any other term.
    ///
    /// # Specification
    /// trivial.
    fn constructed(
        &mut self,
        term: &FreeTerm,
        constructors: &BTreeMap<Name, (Vec<ValueTypeId>, ValueTypeId, ConstructorTag)>,
    ) -> Option<ValueId>
    {
        let mut pending = Vec::from([Step::Read(term.to_node())]);
        let mut built: Vec<ValueId> = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                Step::Read(node) => {
                    let TermView::Ctor { name, args } = node.view()
                    else {
                        return None;
                    };
                    let args: Vec<TermNode<'_>> = args.collect();
                    pending.push(Step::Apply(name, args.len()));
                    pending.extend(args.into_iter().rev().map(Step::Read));
                },
                Step::Apply(name, count) => {
                    let &(ref fields, family, tag) = constructors.get(name)?;
                    let start = built.len().checked_sub(count)?;
                    if fields.len() != count {
                        return None;
                    }
                    let fields = built.split_off(start);
                    built.push(self.arena.value_constructor(family, tag, fields));
                },
            }
        }
        match *built.as_slice() {
            [value] => Some(value),
            _ => None,
        }
    }

    /// Record each node of the index terms `port`'s sort is applied to,
    /// written as `written`, that a constructor of `constructors` heads, at
    /// that constructor's family.
    ///
    /// # Specification
    /// trivial.
    fn index_nodes(
        &mut self,
        port: &SortRef,
        written: &WrittenSort,
        constructors: &BTreeMap<Name, (Vec<ValueTypeId>, ValueTypeId, ConstructorTag)>,
        context: ContextIndex,
    )
    {
        for (term, nodes) in port.arguments.iter().zip(&written.indices) {
            let mut pending = Vec::from([term.to_node()]);
            let mut at = nodes.nodes.iter();
            while let Some(node) = pending.pop() {
                let Some(placed) = at.next()
                else {
                    break;
                };
                if let TermView::Ctor { name, args } = node.view() {
                    if let Some(&(_, family, _)) = constructors.get(name) {
                        self.emit(placed.span, DescribedRole::Term, family, context);
                    }
                    let first = pending.len();
                    pending.extend(args);
                    if let Some(children) = pending.get_mut(first ..) {
                        children.reverse();
                    }
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
    ///   F(…))`, a field a later one names bound by a dependent arrow; each
    ///   field's name at its type where it names no field before it; the
    ///   written result at the family's universe, and each of its arguments
    ///   naming a parameter at that parameter's classifier.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::theory`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Maybe(a)`'s constructors, fields, result and its
    ///   argument answer under `a`, and `List(a)`'s tail, scoped past the
    ///   head's binder, answers at `List(a)`.
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
            let lifted =
                gandr_core_term::shift_value_type(self.arena, classifier, Binders::from(lift));
            classifiers.push(lifted.settle(self.arena));
        }
        for (fields, member) in signature.constructors().iter().zip(&written.constructors) {
            let ty = if fields.is_empty() {
                family
            }
            else {
                gandr_core_term::constructor_classifier(self.arena, family, fields)
            };
            self.emit(member.named, DescribedRole::Name, ty, context);
            let mut earlier = Binders::NONE;
            for (&field, port) in fields.iter().zip(&member.fields) {
                let outside =
                    match gandr_core_term::strengthen_value_type(self.arena, field, earlier) {
                        Maybe::Present(lowered) => Maybe::Present(lowered.settle(self.arena)),
                        Maybe::Absent(reason) => Maybe::Absent(reason),
                    };
                earlier = earlier.deeper();
                if let Maybe::Present(named) = port.named
                    && let Maybe::Present(outside) = outside
                {
                    self.emit(named, DescribedRole::Name, outside, context);
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

    /// Record the type each observation of the codata family `constant`,
    /// whose parameters are `parameters` and whose signature is `signature`,
    /// writes, as `written` keeps it.
    ///
    /// # Specification
    /// - requires: `written` is where the family's reader read its
    ///   observations, in the order `signature` lists them; `kinds` holds the
    ///   universe of each data family the module declares.
    /// - ensures: under the parameters, each node of an observation's type, in
    ///   pre-order, answers at its universe: the family itself at the family's
    ///   kind, a parameter read as a type at the universe its code is read out
    ///   of, a base type at `Type`, and a data family applied at its kind; an
    ///   argument naming a parameter answers at that parameter's classifier,
    ///   and any other argument as the type it quotes. The walk stops at the
    ///   first node no rule above types, so no node answers out of place.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::theory`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Stream(a)`'s observations `head : a` and `tail :
    ///   Stream(a)` answer under `a`: `a` read as a type at `Type`, the family
    ///   at `Type[-]` and its argument at the parameter's classifier; a base
    ///   type observed by an unparameterised family at `Type`.
    /// - witness: `described::tests::a_codata_observation_s_type_answers_at_its_universe`
    fn codata(
        &mut self,
        parameters: &[FamilyParameter],
        written: &WrittenMembers,
        (constant, signature): (ConstantIndex, &CodataSignature),
        kinds: &BTreeMap<ConstantIndex, ValueTypeId>,
    )
    {
        let mut scope = Scope::default();
        for parameter in parameters {
            scope.push(&parameter.name, Dependent(true));
        }
        let context = self.context(&scope);
        let count = signature.parameters().len();
        let mut classifiers = Vec::with_capacity(count);
        for (place, &classifier) in signature.parameters().iter().enumerate() {
            let lift = u32::try_from(count.saturating_sub(place)).unwrap_or(u32::MAX);
            let lifted =
                gandr_core_term::shift_value_type(self.arena, classifier, Binders::from(lift));
            classifiers.push(lifted.settle(self.arena));
        }
        // The classifier of the parameter a variable of the context names.
        let classifier = |index: DeBruijnIndex| {
            let index = usize::try_from(u32::from(index)).ok()?;
            let place = count.checked_sub(index)?.checked_sub(1_usize)?;
            classifiers.get(place).copied()
        };
        for (&observation, member) in signature.observations().iter().zip(&written.observations) {
            let mut nodes = member.ty.nodes.iter();
            let mut pending = match self.arena.comp_type(observation) {
                Some(&CompType::Returner { result, .. }) => Vec::from([Observed::Type(result)]),
                Some(&CompType::Codata {
                    declaration,
                    ref arguments,
                }) if declaration == constant => {
                    let below: Vec<Observed> = arguments
                        .iter()
                        .rev()
                        .map(|&argument| Observed::Value(argument))
                        .collect();
                    let Some(node) = nodes.next()
                    else {
                        continue;
                    };
                    self.emit(node.span, DescribedRole::Type, signature.kind(), context);
                    below
                },
                Some(_) | None => continue,
            };
            while let Some(observed) = pending.pop() {
                let Some(node) = nodes.next()
                else {
                    break;
                };
                let ty = match observed {
                    Observed::Type(ty) => ty,
                    Observed::Value(value) => match self.arena.value(value) {
                        Some(&Value::Quote(ty)) => ty,
                        Some(&Value::Variable { index, .. }) => {
                            let Some(at) = classifier(index)
                            else {
                                break;
                            };
                            self.emit(node.span, DescribedRole::Type, at, context);
                            continue;
                        },
                        Some(_) | None => break,
                    },
                };
                let (universe, below) = match self.arena.value_type(ty) {
                    Some(&ValueType::Base(_)) => (Some(self.universe(Level::zero())), Vec::new()),
                    Some(&ValueType::Product(ref parts)) if parts.is_empty() => {
                        (Some(self.universe(Level::zero())), Vec::new())
                    },
                    Some(&ValueType::Element { ref target, .. }) => {
                        let target = target.clone();
                        (Some(self.universe(target)), Vec::new())
                    },
                    Some(&ValueType::Data {
                        declaration,
                        ref arguments,
                    }) => (
                        kinds.get(&declaration).copied(),
                        arguments
                            .iter()
                            .rev()
                            .map(|&argument| Observed::Value(argument))
                            .collect(),
                    ),
                    Some(_) | None => break,
                };
                let Some(universe) = universe
                else {
                    break;
                };
                self.emit(node.span, DescribedRole::Type, universe, context);
                pending.extend(below);
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
    /// - ensures: for every `theory` block and every unparameterised `data`
    ///   family's operations and rules, each written node at the type its
    ///   member states, as the [`crate::described`] documentation lays out,
    ///   each read in its context; a parameterised family's constructors, and
    ///   those of a family the native reading owns whole, at its native
    ///   signature under its parameters; each node of a codata family's
    ///   observation types at its universe under its parameters; the first
    ///   context is the empty one.
    /// - provides: what a face answers inside a described declaration.
    /// - fails: never; a node no type is stated for records nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a theory's sorts, operations, laws and circuit, a
    ///   data family's operations and rules, and the constructors of a family
    ///   with a function field answer at the types asserted.
    /// - witness: `described::tests::a_theory_answers_at_every_member`
    /// - witness: `described::tests::a_data_rule_answers_each_node_at_its_sort`
    /// - witness: `described::tests::a_family_the_native_reading_owns_answers_at_its_signature`
    /// - witness: `described::tests::a_codata_observation_s_type_answers_at_its_universe`
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
                uses: Vec::new(),
            },
            members: BTreeMap::new(),
        };
        let mut families: BTreeMap<Name, (ValueTypeId, ValueTypeId)> = BTreeMap::new();
        let mut constructors: BTreeMap<Name, (Vec<ValueTypeId>, ValueTypeId, ConstructorTag)> =
            BTreeMap::new();
        let mut signatures: BTreeMap<Name, (ConstantIndex, &DataSignature)> = BTreeMap::new();
        let mut codatas: BTreeMap<Name, (ConstantIndex, &CodataSignature)> = BTreeMap::new();
        let mut kinds: BTreeMap<ConstantIndex, ValueTypeId> = BTreeMap::new();
        let base = typer.universe(Level::zero());
        for (name, atom) in [
            ("Integer", BaseType::Integer),
            ("String", BaseType::String),
            ("Char", BaseType::Character),
            ("u32", BaseType::Fixed(gandr_kernel_term::IntegerWidth::U32)),
            ("u64", BaseType::Fixed(gandr_kernel_term::IntegerWidth::U64)),
            ("i32", BaseType::Fixed(gandr_kernel_term::IntegerWidth::I32)),
            ("i64", BaseType::Fixed(gandr_kernel_term::IntegerWidth::I64)),
        ] {
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
            let (index, signature) = match declaration.outcome() {
                DeclarationOutcome::Data(index) => match self.data(index) {
                    Maybe::Present(signature) => (index, signature),
                    Maybe::Absent(_) => continue,
                },
                DeclarationOutcome::Codata(index) => {
                    if let Maybe::Present(signature) = self.codata(index) {
                        let _first = codatas.insert(
                            Name::from(declaration.name().as_ref()),
                            (declaration.constant(), signature),
                        );
                    }
                    continue;
                },
                DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Completed { .. }
                | DeclarationOutcome::Bodied { .. }
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_) => continue,
            };
            let _first = kinds.insert(declaration.constant(), signature.kind());
            let _first = signatures.insert(
                Name::from(declaration.name().as_ref()),
                (declaration.constant(), signature),
            );
            if !signature.parameters().is_empty() {
                continue;
            }
            let ty = typer
                .arena
                .value_type_data(declaration.constant(), Vec::new());
            let _first = families.insert(
                Name::from(declaration.name().as_ref()),
                (ty, signature.kind()),
            );
            for (tag, (name, fields)) in self
                .constructors(index)
                .iter()
                .zip(signature.constructors())
                .enumerate()
            {
                let _first = constructors.insert(
                    Name::from(name.as_str()),
                    (fields.clone(), ty, ConstructorTag::from(tag)),
                );
            }
        }
        let code = families.get(&Name::from("Theory")).map(|&(ty, _)| ty);
        for described in &self.descriptions().declarations {
            match described.presentation {
                Maybe::Present(ref presentation) => {
                    typer.theory(presentation, &described.written, code);
                },
                Maybe::Absent(_) => {
                    if described.description.polarity == DeclPolarity::Codata {
                        if let Some(&codata) = codatas.get(&described.description.id.name) {
                            typer.codata(&described.parameters, &described.written, codata, &kinds);
                        }
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
                        signatures.get(&described.description.id.name)
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
        // A family the native reading owns whole answers as a parameterised
        // one does, at its signature, under however many parameters it has.
        for native in &self.descriptions().natives {
            if let Some(&(constant, signature)) = signatures.get(&native.name) {
                typer.parameterised(&native.parameters, &native.written, constant, signature);
            }
        }
        typer.types
    }
}

#[cfg(test)]
mod tests;
