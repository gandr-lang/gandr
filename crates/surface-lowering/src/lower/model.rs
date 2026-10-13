//! The lowering half of type families and derived model signatures: a family
//! expanded where it is applied, the type minted for each value component a
//! model signature derives, and the check of each family component's indices
//! against its member's parameters. The design lives with the collection
//! pass (`crate::module::model`).
//!
//! # A derived component is minted as its written spelling lowers
//!
//! An operation `f : (x₁ : S₁, …) => S` mints as the telescope Π the written
//! component `f : (x₁ : S₁, …) => S` lowers to: `+U` over one binder per
//! telescope entry, dependent exactly where a later entry or the result names
//! it, into the returner of the result — the product of the results for a
//! many-out operation. A law mints the same telescope into the returner of
//! `Path(S, l, r)`, an application `g(t₁, …)` in either endpoint as the
//! returned call of the member `g` names, `↑((force g) t₁ …)`, as the written
//! endpoint lowers. A sort mints as what its component reads: the member's
//! type for a strengthened sort, the atom for a sealed one, and the family's
//! type over the index terms for an indexed one. The derived type is therefore
//! the written signature's, node for node, and the checker sees no
//! difference between the two.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CertificateEquality;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::TermId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::Stretch;
use super::exits;
use super::lowered;
use super::stretch;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::error::TelescopeFault;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::model::Binder;
use crate::model::Dependent;
use crate::model::ModelFault;
use crate::model::ModelForm;
use crate::model::ModelSignature;
use crate::model::SortTerm;
use crate::model::Tail;
use crate::model::dependence;
use crate::module::Container;
use crate::module::FamilyForm;
use crate::module::FamilyIndex;
use crate::module::Half;
use crate::module::ModelPart;
use crate::module::Operand;
use crate::module::SlotIndex;
use crate::module::StructureIndex;
use crate::module::TypeMeaning;
use crate::module::spine_domains;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

/// Why a derived type could not be minted.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Missing<'source>
{
    /// A component it names was refused: the refusal it inherits.
    Refused(LoweringRefusal<'source>),
    /// A component it names did not lower.
    Unlowered,
}

/// The binders a derived type is read under: a prefix of its telescope, each
/// with whether it binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Context<'form>
{
    /// The binders in scope, outermost first.
    binders: &'form [Binder],
    /// Whether each binds, in the same order.
    dependent: &'form [Dependent],
}

/// One step of the walk minting a term: a node to read, or an application
/// of the named operation to the last values minted.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Walk<'term>
{
    /// A node whose value is minted next.
    Read(TermNode<'term>),
    /// The operation and its argument count.
    Apply(&'term Name, OperandCount),
}

/// What a derived type is minted for: the module it is read in, its model's
/// operations by name, and the origin every node it mints carries.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Minting<'source>
{
    /// The module the type is read in.
    structure: StructureIndex,
    /// Each operation of the model, by its name in the sign, with the
    /// member name it reads in the module.
    operations: BTreeMap<Name, SurfaceName<'source>>,
    /// The origin every minted node carries.
    origin: Origin,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Seed every type family member: each parameter's type under the
    /// parameters before it, and the family's type under all of them; and
    /// each written family kind at the outermost frame.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: one frame per parameter, typed with its written type and
    ///   mentioned, so every parameter binds in the family's type, and one seed
    ///   per type the members and kinds write, appended to `seeds`.
    /// - provides: the family half of [`Self::seed`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-parameter family whose type names both
    ///   parameters lowers with both bound.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(
        captures: before = seeds.len(),
        ensures: seeds.len() >= before,
    )]
    pub(super) fn seed_families(
        &mut self,
        seeds: &mut Vec<(NodeIndex, Reading)>,
    )
    {
        for family in &self.collected.families {
            let mut frame = Frame::Outermost;
            for parameter in &family.parameters {
                seeds.push((parameter.classifier.node, Reading::ValueType(frame)));
                let name = SurfaceName::from(self.text_at(parameter.named));
                let bound = self.scope.extend_typed(
                    frame,
                    name,
                    parameter.classifier.node,
                    Maybe::Present(parameter.named.span),
                );
                self.scope.mention(bound);
                frame = Frame::Inner(bound);
            }
            seeds.push((family.defined.node, Reading::ValueType(frame)));
        }
        for check in self.collected.family_checks.values() {
            if let FamilyForm::Written(kind) = check.stated {
                seeds.push((kind.node, Reading::ValueType(Frame::Outermost)));
            }
        }
    }

    /// Classify the type family `family`, whose refusal `held` carries,
    /// applied to the arguments `applied` holds in the operand store.
    ///
    /// # Specification
    /// - requires: `applied` is a stretch of the operand store.
    /// - ensures: the family stands as a value type over its arguments, each
    ///   read as a value under the site's frame, and the reference is recorded
    ///   against `held`, so a refused family refuses the declaration naming it.
    /// - fails: the arity refusal for an argument count other than the family's
    ///   parameter count; the wrong-sort refusal where no value type is read or
    ///   reached.
    /// - panics: none.
    ///
    /// # Errors
    /// The family's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Hom(a, b)` expands, and `Hom(a)` is refused by its
    ///   arity.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_family_applied_to_too_few_indices_is_refused`
    #[spec(ensures: |ret| ret.is_err() || self.plans.get(usize::from(site.at.node)) == Some(&Plan::Expansion(family, applied)))]
    pub(super) fn expansion(
        &mut self,
        site: Site,
        family: FamilyIndex,
        held: SlotIndex,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let count = applied.end.saturating_sub(applied.start);
        let arity = self
            .collected
            .families
            .get(family.0)
            .map_or(0_usize, |member| member.parameters.len());
        if count != arity {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        }
        let frame = self.require(site, Produced::ValueType)?;
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }
        self.manifests.push((held, site.at.node));
        self.plan(site, Plan::Expansion(family, applied));

        Ok(())
    }

    /// Mint the family `family` over the arguments `arguments` names in the
    /// operand store.
    ///
    /// # Specification
    /// - requires: the family's type and every argument are minted or absent.
    /// - ensures: as [`Self::expand`] over the arguments' values; nothing when
    ///   an argument did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::expansion`].
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_expansion(
        &self,
        family: FamilyIndex,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut values = Vec::new();
        for &argument in stretch(&self.operands, arguments) {
            match self.value_at(argument) {
                | Maybe::Present(value) => values.push(value),
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }

        self.expand(family, &values, sink, origin)
            .map(Lowered::ValueType)
    }

    /// The type of the family `family` with `arguments` for its parameters.
    ///
    /// # Specification
    /// - requires: every argument is a value of the context the result is read
    ///   in.
    /// - ensures: the family's type with the parameter at place `i` replaced by
    ///   `arguments[i]`, each node the substitution mints carrying the origin
    ///   of the node it rewrote, or `origin` for one it built; nothing when the
    ///   type did not lower or the count is not the family's.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Hom(a, a)` is the member's type with both parameters
    ///   at `a`.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
    fn expand(
        &self,
        family: FamilyIndex,
        arguments: &[ValueId],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let Some(member) = self.collected.families.get(family.0)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        if member.parameters.len() != arguments.len() {
            return Maybe::Absent(lowered::Absent::Unminted);
        }
        let defined = match self.value_type_at(member.defined.node) {
            | Maybe::Present(defined) => defined,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let environment: Vec<ValueId> = arguments.iter().rev().copied().collect();
        let mark = sink.arena.watermark();
        let code = sink.arena.value_quote(defined);
        let mut carried = Vec::new();
        let substituted = gandr_core_term::substitute_environment_traced(
            sink.arena,
            TermId::Value(code),
            &environment,
            &mut carried,
        );
        exits::record_copies(sink, mark, &carried, origin);
        let TermId::Value(substituted) = substituted
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let Some(&Value::Quote(expanded)) = sink.arena.value(substituted)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };

        Maybe::Present(expanded)
    }

    /// Mint the type every model half derives, and refuse each one naming a
    /// component that did not lower.
    ///
    /// # Specification
    /// - requires: the mint sweep and the abstract slots have run.
    /// - ensures: every unrefused slot whose signature is a model half holds
    ///   the type its derived component mints, its origin the ascription's
    ///   sign; a slot whose component names a refused one holds that refusal as
    ///   a fault, and one naming a component that did not lower holds
    ///   [`LoweringRefusal::UnstatedComponent`] with [`ModelFault::Inherited`].
    /// - provides: the declared types [`Self::outcome`] reads for model halves.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CatShape` operations and laws mint the written
    ///   signature's types, and a law over a refused family inherits it.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_family_of_the_wrong_telescope_is_refused`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body sweeps every slot once, filing each model half; the check looks each filed half up among the faults once"
        )
    )]
    #[spec(
        ensures: self.modelled.keys().all(|slot| !self.faults.contains_key(slot)),
    )]
    pub(super) fn mint_models(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let mut modelled = BTreeMap::new();
        let mut faults = BTreeMap::new();
        for (position, slot) in self.collected.slots.iter().enumerate() {
            let (
                Maybe::Present(Half {
                    declaration,
                    operand: Operand::Model(part),
                }),
                Maybe::Absent(_),
                Container::Module(structure),
            ) = (slot.signature, slot.refusal, slot.container)
            else {
                continue;
            };
            let Maybe::Present(origin) = self.origin_at(declaration.node)
            else {
                continue;
            };
            let position = SlotIndex::from(position);
            match self.mint_component(structure, part, sink, origin) {
                | Ok(minted) => {
                    let _first = modelled.insert(position, minted);
                },
                | Err(Missing::Refused(refusal)) => {
                    let _first = faults.insert(position, refusal);
                },
                | Err(Missing::Unlowered) => {
                    let _first = faults.insert(position, LoweringRefusal::UnstatedComponent {
                        span: declaration.span,
                        name: slot.name,
                        fault: ModelFault::Inherited,
                    });
                },
            }
        }
        self.modelled.extend(modelled);
        self.faults.extend(faults);
    }

    /// The type the value component at `part` derives, read in the module at
    /// `structure`.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: an operation's or a law's telescope Π, as the module's
    ///   documentation states it, every node carrying `origin`.
    /// - fails: a component the derivation cannot state or that is a sort, and
    ///   one naming a component that did not lower, as unlowered; one naming a
    ///   refused component, with its refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_models`].
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value_type(id).is_some()))]
    fn mint_component(
        &self,
        structure: StructureIndex,
        part: ModelPart,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<ValueTypeId, Missing<'source>>
    {
        let Some(model) = self.collected.models.get(part.model.0)
        else {
            return Err(Missing::Unlowered);
        };
        let Some(Ok(form)) = model
            .components
            .get(part.component.0)
            .map(|component| component.form.as_ref())
        else {
            return Err(Missing::Unlowered);
        };
        let (telescope, tail) = match *form {
            | ModelForm::Operation {
                ref telescope,
                ref results,
            } => (telescope, Tail::Results(results)),
            | ModelForm::Law {
                ref telescope,
                ref carrier,
                ref left,
                ref right,
            } => (telescope, Tail::Path(carrier, left, right)),
            | ModelForm::Sort { .. } => return Err(Missing::Unlowered),
        };
        let minting = Minting {
            structure,
            operations: self.operation_names(model),
            origin,
        };
        let dependent = dependence(telescope, tail);
        let mut domains = Vec::with_capacity(telescope.len());
        for (depth, binder) in telescope.iter().enumerate() {
            let context = Context {
                binders: telescope.get(.. depth).unwrap_or_default(),
                dependent: dependent.get(.. depth).unwrap_or_default(),
            };
            domains.push(self.sort_type(&binder.sort, context, &minting, sink)?);
        }
        let context = Context {
            binders: telescope,
            dependent: &dependent,
        };
        let codomain = match tail {
            | Tail::Results(results) => {
                let mut sorts = Vec::with_capacity(results.len());
                for result in results {
                    sorts.push(self.sort_type(result, context, &minting, sink)?);
                }
                match *sorts.as_slice() {
                    | [one] => one,
                    | _ => {
                        let id = sink.arena.value_type_product(&sorts);
                        sink.origins.record_value_type(id, origin);
                        id
                    },
                }
            },
            | Tail::Path(carrier, left, right) => {
                let over = self.sort_type(carrier, context, &minting, sink)?;
                let from = self.term_value(left, context, &minting, sink)?;
                let to = self.term_value(right, context, &minting, sink)?;
                let id = sink.arena.value_type_path(over, from, to);
                sink.origins.record_value_type(id, origin);
                id
            },
        };
        let mut chain = sink.arena.comp_type_returner(codomain);
        sink.origins.record_comp_type(chain, origin);
        for (&domain, &binds) in domains.iter().zip(&dependent).rev() {
            chain = if binds.0 {
                sink.arena.comp_type_pi(domain, chain)
            }
            else {
                sink.arena.comp_type_arrow(domain, chain)
            };
            sink.origins.record_comp_type(chain, origin);
        }
        let id = sink.arena.value_type_thunk(chain);
        sink.origins.record_value_type(id, origin);

        Ok(id)
    }

    /// Each operation of `model`, by its name in the sign, with the member
    /// name the module reads it under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per operation component, its name tile's text the
    ///   member name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp` and `id` are found for the `CatShape` laws.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| ret.len() <= model.components.len())]
    fn operation_names(
        &self,
        model: &ModelSignature,
    ) -> BTreeMap<Name, SurfaceName<'source>>
    {
        model
            .components
            .iter()
            .filter(|component| matches!(component.form, Ok(ModelForm::Operation { .. })))
            .map(|component| (component.name.clone(), self.name_at(component.named)))
            .collect()
    }

    /// The type the sort term `sort` names, read under `context`.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: for an unindexed sort, the type its component reads — the
    ///   member's type, or the atom a sealed component declares; for an indexed
    ///   one, its family expanded over the index terms' values.
    /// - fails: a sort no type component of the module answers, of another
    ///   index count, or whose type did not lower, as unlowered; one whose
    ///   component is refused, with its refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Ob` reads the universe the member writes and `Hom(a,
    ///   b)` the member's family over two variables.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value_type(id).is_some()))]
    fn sort_type(
        &self,
        sort: &SortTerm,
        context: Context<'_>,
        minting: &Minting<'source>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueTypeId, Missing<'source>>
    {
        let Some(component) = self
            .collected
            .structures
            .get(usize::from(minting.structure))
            .and_then(|structure| {
                structure
                    .types
                    .iter()
                    .find(|component| component.name.as_ref() == sort.sort.as_ref())
            })
            .copied()
        else {
            return Err(Missing::Unlowered);
        };
        if let Some(Maybe::Present((_at, refusal))) = self
            .collected
            .slots
            .get(usize::from(component.held))
            .map(|held| held.refusal)
        {
            return Err(Missing::Refused(refusal));
        }
        match (component.meaning, sort.indices.is_empty()) {
            | (TypeMeaning::Manifest(defined), true) => match self.value_type_at(defined.node) {
                | Maybe::Present(id) => Ok(id),
                | Maybe::Absent(_) => Err(Missing::Unlowered),
            },
            | (TypeMeaning::Sealed, true) => {
                let Some(atom) = self.collected.slots.get(usize::from(component.held))
                else {
                    return Err(Missing::Unlowered);
                };
                let id = sink.arena.value_type_abstract(atom.constant);
                sink.origins.record_value_type(id, minting.origin);
                Ok(id)
            },
            | (TypeMeaning::Instantiated { defined, instance }, true) => self
                .instance_types
                .get(&(instance, defined.node))
                .copied()
                .ok_or(Missing::Unlowered),
            | (TypeMeaning::Family(family), false) => {
                let mut arguments = Vec::with_capacity(sort.indices.len());
                for index in &sort.indices {
                    arguments.push(self.term_value(index, context, minting, sink)?);
                }
                match self.expand(family, &arguments, sink, minting.origin) {
                    | Maybe::Present(id) => Ok(id),
                    | Maybe::Absent(_) => Err(Missing::Unlowered),
                }
            },
            | (
                TypeMeaning::Manifest(_) | TypeMeaning::Sealed | TypeMeaning::Instantiated { .. },
                false,
            )
            | (TypeMeaning::Family(_), true) => Err(Missing::Unlowered),
        }
    }

    /// The value the term `term` denotes, read under `context`.
    ///
    /// # Specification
    /// - requires: every operation `term` applies is a member of the module.
    /// - ensures: a variable is the intuitionistic index counting the binding
    ///   binders after it in `context`; an application `g(t₁, …, tₙ)` is
    ///   `↑((force g) t₁ … tₙ)` over the constant of the member `g` names,
    ///   every node carrying the minting's origin.
    /// - fails: a variable `context` does not bind, a constructor or results
    ///   term, and an operation the module does not define, as unlowered.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing::Unlowered`].
    ///
    /// # Termination
    /// The walk pushes each node of the finite term once and pops each step
    /// once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CatShape` law endpoints mint the written
    ///   endpoints' values.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value(id).is_some()))]
    fn term_value(
        &self,
        term: &FreeTerm,
        context: Context<'_>,
        minting: &Minting<'source>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueId, Missing<'source>>
    {
        let origin = minting.origin;
        let mut pending = Vec::from([Walk::Read(term.to_node())]);
        let mut built: Vec<ValueId> = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                | Walk::Read(node) => match node.view() {
                    | TermView::Var(name) => {
                        let index = variable(context, name)?;
                        let id = sink.arena.value_variable(Zone::Intuitionistic, index);
                        sink.origins.record_value(id, origin);
                        built.push(id);
                    },
                    | TermView::Op { name, args } => {
                        let arguments: Vec<TermNode<'_>> = args.collect();
                        pending.push(Walk::Apply(name, OperandCount::from(arguments.len())));
                        pending.extend(arguments.into_iter().rev().map(Walk::Read));
                    },
                    | TermView::Ctor { .. } | TermView::Results { .. } => {
                        return Err(Missing::Unlowered);
                    },
                },
                | Walk::Apply(name, count) => {
                    let start = built
                        .len()
                        .checked_sub(usize::from(count))
                        .ok_or(Missing::Unlowered)?;
                    let arguments: Vec<ValueId> = built.drain(start ..).collect();
                    let constant = self.operation_constant(minting, name)?;
                    let head = sink.arena.value_constant(constant);
                    sink.origins.record_value(head, origin);
                    let mut applied = sink.arena.computation_force(head);
                    sink.origins.record_computation(applied, origin);
                    for argument in arguments {
                        applied = sink.arena.computation_application(applied, argument);
                        sink.origins.record_computation(applied, origin);
                    }
                    let returned = sink.arena.value_returned(applied);
                    sink.origins.record_value(returned, origin);
                    built.push(returned);
                },
            }
        }
        match *built.as_slice() {
            | [value] => Ok(value),
            | _ => Err(Missing::Unlowered),
        }
    }

    /// The constant of the member the operation `name` reads in the
    /// minting's module.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the admission position of the member the module declares
    ///   under the operation's name.
    /// - fails: an operation the model does not declare, or one the module does
    ///   not define, as unlowered; a refused member, with its refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp` reads the member `comp`.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| ret.is_err() || minting.operations.contains_key(name))]
    fn operation_constant(
        &self,
        minting: &Minting<'source>,
        name: &Name,
    ) -> Result<ConstantIndex, Missing<'source>>
    {
        let Some(&member) = minting.operations.get(name)
        else {
            return Err(Missing::Unlowered);
        };
        let Some(&slot) = self
            .collected
            .by_name
            .get(&(Container::Module(minting.structure), member))
        else {
            return Err(Missing::Unlowered);
        };
        let Some(declared) = self.collected.slots.get(usize::from(slot))
        else {
            return Err(Missing::Unlowered);
        };
        if let Maybe::Present((_at, refusal)) = declared.refusal {
            return Err(Missing::Refused(refusal));
        }

        Ok(declared.constant)
    }

    /// Check every family component's indices against its member's
    /// parameters, and declare each written kind's check.
    ///
    /// # Specification
    /// - requires: the mint sweep and the model halves have run.
    /// - ensures: a check slot whose index at some place, read with every index
    ///   before it bound, is not syntactically its parameter's type holds
    ///   [`LoweringRefusal::FamilyTelescope`] at the first such place, counted
    ///   from one; a written kind that agrees declares the check of the family
    ///   at the kind, `thunk (λ … λ. return ⌜τ⌝)`; an index whose sort is
    ///   refused holds that refusal; a kind whose indices do not lower holds
    ///   [`LoweringRefusal::UnreadAscription`].
    /// - provides: the family half of [`Self::outcome`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the written and derived `CatShape` families agree,
    ///   and a family whose parameter is at another type is refused naming it.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_family_of_the_wrong_telescope_is_refused`
    /// - witness: `modules::modules::models::a_written_family_of_the_wrong_telescope_is_refused`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body checks every family check once; the check looks each up among the faults and the kind checks once"
        )
    )]
    #[spec(
        ensures: self.collected.family_checks.keys().all(|slot| !(self.faults.contains_key(slot) && self.kind_checks.contains_key(slot))),
    )]
    pub(super) fn check_families(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let mut faults = BTreeMap::new();
        let mut checks = BTreeMap::new();
        for (&slot, check) in &self.collected.family_checks {
            let (Some(declared), Some(family)) = (
                self.collected.slots.get(usize::from(slot)),
                self.collected.families.get(check.family.0),
            )
            else {
                continue;
            };
            if let Maybe::Present(_) = declared.refusal {
                continue;
            }
            let Maybe::Present(origin) = self.origin_at(declared.named.node)
            else {
                continue;
            };
            let mut parameters = Vec::with_capacity(family.parameters.len());
            for parameter in &family.parameters {
                match self.value_type_at(parameter.classifier.node) {
                    | Maybe::Present(id) => parameters.push(id),
                    | Maybe::Absent(_) => break,
                }
            }
            if parameters.len() != family.parameters.len() {
                continue;
            }
            let indices = match check.stated {
                | FamilyForm::Written(kind) => self.written_indices(kind, sink, origin),
                | FamilyForm::Derived => {
                    self.derived_indices(check.structure, check.component, sink, origin)
                },
            };
            let indices = match indices {
                | Ok(indices) => indices,
                | Err(missing) => {
                    let refusal = match missing {
                        | Missing::Refused(refusal) => refusal,
                        | Missing::Unlowered => LoweringRefusal::UnreadAscription {
                            span: declared.named.span,
                            name: declared.name,
                            form: crate::error::AscriptionForm::Kinded,
                        },
                    };
                    let _first = faults.insert(slot, refusal);
                    continue;
                },
            };
            let disagreeing = indices
                .iter()
                .zip(&parameters)
                .position(|(&index, &parameter)| {
                    gandr_core_term::equal_type_syntax(sink.arena, index, parameter)
                        != CertificateEquality::Equal
                });
            if let Some(place) = disagreeing {
                let span = self
                    .collected
                    .slots
                    .get(usize::from(family.held))
                    .map_or(declared.named.span, |held| held.named.span);
                let _first = faults.insert(slot, LoweringRefusal::FamilyTelescope {
                    span,
                    name: declared.name,
                    fault: TelescopeFault::Index(OperandCount::from(place.saturating_add(1))),
                });
                continue;
            }
            if let FamilyForm::Written(kind) = check.stated
                && let Maybe::Present(witness) = self.family_witness(
                    kind,
                    family.defined,
                    OperandCount::from(family.parameters.len()),
                    sink,
                    origin,
                )
            {
                let _first = checks.insert(slot, witness);
            }
        }
        self.faults.extend(faults);
        self.kind_checks.extend(checks);
    }

    /// Each index type the written kind `kind` states, read with the indices
    /// before it bound.
    ///
    /// The kind's plan is spent by the mint sweep, so its entries are read
    /// again from its domain, as the telescope and value function readers
    /// read them; their types and readings outlive the sweep.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: one type per entry of the kind's domain — each entry of a
    ///   parenthesised list, the domain itself when written bare, or each
    ///   domain along a static arrow's spine — each carried into the context
    ///   binding every entry before it.
    /// - fails: [`Missing::Refused`] with the reader's refusal for a domain
    ///   whose pieces or entries do not read, and [`Missing::Unlowered`] for an
    ///   empty kind, a list without its opener, or an entry that did not lower.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `(a : Ob, b : Ob) => Type` states `Ob` twice, the
    ///   second carried under the first, and `Type -> Type -> Type` states
    ///   `Type` twice.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_written_family_of_the_wrong_telescope_is_refused`
    /// - witness: `modules::modules::a_kinded_type_component_spine_declares_its_arity`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |types| types.iter().all(|&id| sink.arena.value_type(id).is_some())))]
    fn written_indices(
        &self,
        kind: Placed,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<Vec<ValueTypeId>, Missing<'source>>
    {
        if let Ok(Some((_, Former::ArrowType))) = self.form_at(kind) {
            let domains = spine_domains(self.pbg, self.tree, kind).map_err(Missing::Refused)?;
            let mut indices = Vec::with_capacity(domains.len());
            for domain in domains {
                let Maybe::Present(id) = self.value_type_at(domain.node)
                else {
                    return Err(Missing::Unlowered);
                };
                let frame = self.reading(domain.node).frame();
                indices.push(self.relocate_value_type(id, frame, sink, origin));
            }
            return Ok(indices);
        }
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, kind.node, &mut pieces).map_err(Missing::Refused)?;
        let Some(domain) = pieces.pieces.iter().find_map(|piece| match *piece {
            | Piece::Operand(operand) => Some(operand),
            | Piece::Tile { .. } => None,
        })
        else {
            return Err(Missing::Unlowered);
        };
        let entries: Vec<NodeIndex> = match self.form_at(domain) {
            | Ok(Some((name, Former::ParenthesizedType))) => {
                let mut listed = Pieces::new();
                read_pieces(self.pbg, self.tree, domain.node, &mut listed)
                    .map_err(Missing::Refused)?;
                let mut cursor = Cursor::new(&listed.pieces, domain.span);
                if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
                    return Err(Missing::Unlowered);
                }
                let list = Site {
                    at: domain,
                    name,
                    reading: self.reading(domain.node),
                };
                self.type_entries(list, &mut cursor, TileName::PAREN_CLOSE)
                    .map_err(Missing::Refused)?
                    .iter()
                    .map(|entry| entry.held.at().node)
                    .collect()
            },
            | Ok(_) => Vec::from([domain.node]),
            | Err(refusal) => return Err(Missing::Refused(refusal)),
        };
        let mut indices = Vec::with_capacity(entries.len());
        for entry in entries {
            let Maybe::Present(id) = self.value_type_at(entry)
            else {
                return Err(Missing::Unlowered);
            };
            let frame = self.reading(entry).frame();
            indices.push(self.relocate_value_type(id, frame, sink, origin));
        }

        Ok(indices)
    }

    /// Each index type the derived sort at `component` of the module at
    /// `structure` states, read with the indices before it bound.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: one type per derived index binder, every binder before it
    ///   binding.
    /// - fails: [`Missing::Unlowered`] for a component that is no sort, and an
    ///   index's own failure when its sort does not mint.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Hom(dom : Ob, cod : Ob)` states `Ob` twice.
    /// - witness: `modules::modules::models::a_family_of_the_wrong_telescope_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |types| types.iter().all(|&id| sink.arena.value_type(id).is_some())))]
    fn derived_indices(
        &self,
        structure: StructureIndex,
        component: crate::module::ComponentPlace,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<Vec<ValueTypeId>, Missing<'source>>
    {
        let Some(Maybe::Present(model)) = self
            .collected
            .structures
            .get(usize::from(structure))
            .map(|entry| entry.model)
        else {
            return Err(Missing::Unlowered);
        };
        let Some(Ok(form)) = self
            .collected
            .models
            .get(model.0)
            .and_then(|signature| signature.components.get(component.0))
            .map(|derived| derived.form.as_ref())
        else {
            return Err(Missing::Unlowered);
        };
        let ModelForm::Sort {
            indices: ref binders,
        } = *form
        else {
            return Err(Missing::Unlowered);
        };
        let minting = Minting {
            structure,
            operations: BTreeMap::new(),
            origin,
        };
        let dependent: Vec<Dependent> = binders.iter().map(|_| Dependent(true)).collect();
        let mut indices = Vec::with_capacity(binders.len());
        for (depth, binder) in binders.iter().enumerate() {
            let context = Context {
                binders: binders.get(.. depth).unwrap_or_default(),
                dependent: dependent.get(.. depth).unwrap_or_default(),
            };
            indices.push(self.sort_type(&binder.sort, context, &minting, sink)?);
        }

        Ok(indices)
    }

    /// The check of the family whose type is at `defined`, over `arity`
    /// parameters, at the written kind `kind`.
    ///
    /// A telescope kind classifies a value function, so the family checks as
    /// the thunk of its lambdas; a static arrow classifies a type operator, so
    /// it checks as the static abstraction of its code, which the checker
    /// forms at the arrow's classifiers first.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: the kind's type and, for a static arrow, `λ … λ. ⌜τ⌝`, one
    ///   static abstraction per parameter; otherwise `thunk (λ … λ. return
    ///   ⌜τ⌝)`, one lambda per parameter; every node carrying `origin`; nothing
    ///   when the kind or the family's type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the written `CatShape` family checks its member at
    ///   its kind, and a family read against a static arrow checks as an
    ///   operator.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::a_kinded_type_component_forms_at_its_classifier`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present((kind_id, body)) if sink.arena.value_type(kind_id).is_some() && sink.arena.value(body).is_some()))]
    fn family_witness(
        &self,
        kind: Placed,
        defined: Placed,
        arity: OperandCount,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<(ValueTypeId, ValueId), lowered::Absent>
    {
        let (Maybe::Present(stated), Maybe::Present(family)) = (
            self.value_type_at(kind.node),
            self.value_type_at(defined.node),
        )
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let code = sink.arena.value_quote(family);
        sink.origins.record_value(code, origin);
        if let Ok(Some((_, Former::ArrowType))) = self.form_at(kind) {
            let mut operator = code;
            for _parameter in 0 .. usize::from(arity) {
                operator = sink.arena.value_static_lambda(operator);
                sink.origins.record_value(operator, origin);
            }
            return Maybe::Present((stated, operator));
        }
        let mut body = sink.arena.computation_return(code);
        sink.origins.record_computation(body, origin);
        for _parameter in 0 .. usize::from(arity) {
            body = sink.arena.computation_lambda(body);
            sink.origins.record_computation(body, origin);
        }
        let thunk = sink.arena.value_thunk(body);
        sink.origins.record_value(thunk, origin);

        Maybe::Present((stated, thunk))
    }
}

/// The index of the variable `name` read under `context`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for the innermost binder of the name, when it binds, the count of
///   binding binders after it.
/// - fails: [`Missing::Unlowered`] for a name no binding binder bears.
/// - panics: none.
///
/// # Errors
/// [`Missing::Unlowered`].
///
/// # Adequacy
/// - hypothesis: L3 — `a` under `comp`'s five binders counts `b` and `c`.
/// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
#[spec(ensures: |ret| ret.is_err() || context.binders.iter().any(|binder| binder.name == *name))]
fn variable<'source>(
    context: Context<'_>,
    name: &Name,
) -> Result<DeBruijnIndex, Missing<'source>>
{
    let Some(place) = context
        .binders
        .iter()
        .rposition(|binder| binder.name == *name)
    else {
        return Err(Missing::Unlowered);
    };
    if !context.dependent.get(place).is_some_and(|binds| binds.0) {
        return Err(Missing::Unlowered);
    }
    let after = context
        .dependent
        .get(place.saturating_add(1) ..)
        .unwrap_or_default()
        .iter()
        .filter(|binds| binds.0)
        .count();

    Ok(DeBruijnIndex::from(
        u32::try_from(after).unwrap_or(u32::MAX),
    ))
}
