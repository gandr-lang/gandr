//! The lowering half of a functor application: the renaming each instance
//! reads its template through, the types its manifest components read, and
//! the declarations its witnesses and its body's image amount to. The design
//! lives with the collection pass (`crate::module::functor`).

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Carried;
use gandr_core_term::Renaming;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::rename_value_traced;
use gandr_core_term::rename_value_type_traced;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteOffset;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Sink;
use super::Site;
use super::Universe;
use super::exits::record_copies;
use super::lowered;
use crate::error::LoweringRefusal;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::read_pieces;
use crate::module::Container;
use crate::module::DeclarationOutcome;
use crate::module::InstanceIndex;
use crate::module::Matched;
use crate::module::Member;
use crate::module::ParameterForm;
use crate::module::Role;
use crate::module::Sealing;
use crate::module::SlotIndex;
use crate::module::Stratum;
use crate::module::StructureIndex;
use crate::module::TypeComponent;
use crate::module::TypeMeaning;
use crate::origin::Origin;
use crate::resolve::SurfaceName;

impl<'source> Lowerer<'_, 'source>
{
    /// Refuse a path read off the application `target`, `F(X).x` or
    /// `F(X).T`, when its head names a functor.
    ///
    /// # Specification
    /// - requires: `target` is a call or a type application a path selects
    ///   from; `chain` is scratch.
    /// - ensures: nothing when the application's head names no functor, so the
    ///   caller refuses the form as it otherwise would.
    /// - provides: the one refusal a path off an application meets, whatever
    ///   position it is read at.
    /// - fails: [`LoweringRefusal::ProjectionFromApplication`] at the
    ///   application, naming the functor, when the head names one;
    ///   [`LoweringRefusal::UnknownMold`] for a node of a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value path and a type path off an application of a
    ///   functor are each refused by name, and a path off a call of a function
    ///   is not.
    /// - witness: `modules::modules::functors::an_application_is_bound_before_anything_projects_from_it`
    #[spec(ensures: |ret| match ret {
        | Err(LoweringRefusal::ProjectionFromApplication { span, functor }) => span == target.span && self.collected.functors.iter().any(|found| found.name == functor),
        | Err(_) | Ok(()) => true,
    })]
    pub(super) fn refuse_applied(
        &self,
        target: Placed,
        chain: &mut Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        read_pieces(self.pbg, self.tree, target.node, chain)?;
        let Some(&(Piece::Operand(head) | Piece::Tile { at: head, .. })) = chain.pieces.first()
        else {
            return Ok(());
        };
        let name = self.name_at(head);
        if self
            .collected
            .functors
            .iter()
            .any(|functor| functor.name == name)
        {
            return Err(LoweringRefusal::ProjectionFromApplication {
                span: target.span,
                functor: name,
            });
        }

        Ok(())
    }

    /// The parameter module the path head `head` names at `site`: the
    /// parameter of the functor whose body or parameter the declaration
    /// owning `site` belongs to, when it is named `head`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: walking out from the container of the declaration owning
    ///   `site` by an explicit loop, the first functor's body or parameter met
    ///   answers with its parameter when the parameter is named `head`; absent
    ///   otherwise, and for a site no declaration owns.
    /// - provides: the scope a functor's body reads its parameter's components
    ///   through, ahead of the outermost scope.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body reads its parameter's type and value by path,
    ///   and a declaration outside the functor does not.
    /// - witness: `modules::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `modules::modules::functors::a_parameter_is_read_only_inside_its_functor`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(parameter) => self.collected.functors.iter().any(|functor| functor.parameter == parameter && functor.parameter_name == head),
        | Maybe::Absent(_) => true,
    })]
    fn parameter_named(
        &self,
        site: Site,
        head: SurfaceName<'source>,
    ) -> Maybe<StructureIndex, parameter_path::Absent>
    {
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Maybe::Absent(parameter_path::Absent::Outside);
        };
        let mut container = self
            .collected
            .slots
            .get(usize::from(own))
            .map_or(Container::TopLevel, |slot| slot.container);
        while let Container::Module(module) = container
            && let Some(structure) = self.collected.structures.get(usize::from(module))
        {
            if let Stratum::Functor(functor) | Stratum::Parameter(functor) = structure.stratum {
                return match self.collected.functors.get(usize::from(functor)) {
                    | Some(found) if found.parameter_name == head => {
                        Maybe::Present(found.parameter)
                    },
                    | Some(_) | None => Maybe::Absent(parameter_path::Absent::Outside),
                };
            }
            container = structure.container;
        }

        Maybe::Absent(parameter_path::Absent::Outside)
    }

    /// Plan the value path `head.selected`, written at `site`, when `head`
    /// names the parameter of the functor the path is written in.
    ///
    /// # Specification
    /// - requires: `site` is a selection whose only link selects `selected` off
    ///   the head `head`, or `deeper` marks a longer chain.
    /// - ensures: a head naming no parameter here is left to the outermost
    ///   scope, untouched; a one-link path to a value component of the
    ///   parameter stands as that component's template constant, which every
    ///   application renames to its witness.
    /// - provides: the parameter half of [`Self::projection`].
    /// - fails: [`LoweringRefusal::UnknownMember`] naming the parameter and the
    ///   selected name for a component the parameter does not state, or any
    ///   selection past it, since a parameter states no module.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body reads a parameter's value, and a name the
    ///   parameter does not state is refused by name.
    /// - witness: `modules::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `modules::modules::functors::a_parameter_is_read_only_inside_its_functor`
    #[spec(ensures: |ret| match ret {
        | Ok(Read::Unread) => matches!(self.parameter_named(site, self.name_at(head)), Maybe::Absent(_)),
        | Ok(Read::Planned) => matches!(self.plans.get(usize::from(site.at.node)), Some(&super::Plan::Constant(_))),
        | Err(_) => true,
    })]
    pub(super) fn parameter_value(
        &mut self,
        site: Site,
        head: Placed,
        selected: Placed,
        deeper: Deeper,
    ) -> Result<Read, LoweringRefusal<'source>>
    {
        let name = self.name_at(head);
        let Maybe::Present(parameter) = self.parameter_named(site, name)
        else {
            return Ok(Read::Unread);
        };
        let member = self.name_at(selected);
        let unknown = LoweringRefusal::UnknownMember {
            span: selected.span,
            module: name,
            member,
        };
        if deeper.0 {
            return Err(unknown);
        }
        let found = self
            .collected
            .structures
            .get(usize::from(parameter))
            .and_then(|structure| {
                structure.exports.iter().find_map(|&export| match export {
                    | Member::Slot(slot)
                        if self
                            .collected
                            .slots
                            .get(usize::from(slot))
                            .is_some_and(|entry| entry.name == member) =>
                    {
                        Some(slot)
                    },
                    | Member::Slot(_) | Member::Module(_) => None,
                })
            });
        let Some(slot) = found
        else {
            return Err(unknown);
        };
        self.select(site, slot)?;

        Ok(Read::Planned)
    }

    /// Plan the type path `head.selected`, written at `site`, when `head`
    /// names the parameter of the functor the path is written in.
    ///
    /// # Specification
    /// - requires: as [`Self::parameter_value`], for a type path.
    /// - ensures: a head naming no parameter here is left to the outermost
    ///   scope, untouched; a one-link path to a type component of the parameter
    ///   stands for what it reads: an abstract one's template atom, which every
    ///   application renames to the argument's type, or the type a manifest one
    ///   states.
    /// - provides: the parameter half of [`Self::type_path`].
    /// - fails: [`LoweringRefusal::UnknownMember`] as
    ///   [`Self::parameter_value`]; what [`Self::stated_type`] refuses.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body's signature reads the parameter's abstract
    ///   type, and a type the parameter does not state is refused by name.
    /// - witness: `modules::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `modules::modules::functors::a_parameter_is_read_only_inside_its_functor`
    #[spec(ensures: |ret| match ret {
        | Ok(Read::Unread) => matches!(self.parameter_named(site, self.name_at(head)), Maybe::Absent(_)),
        | Ok(Read::Planned) => matches!(self.plans.get(usize::from(site.at.node)), Some(&(super::Plan::Sealed(_) | super::Plan::Transparent(_)))),
        | Err(_) => true,
    })]
    pub(super) fn parameter_type(
        &mut self,
        site: Site,
        head: Placed,
        selected: Placed,
        deeper: Deeper,
    ) -> Result<Read, LoweringRefusal<'source>>
    {
        let name = self.name_at(head);
        let Maybe::Present(parameter) = self.parameter_named(site, name)
        else {
            return Ok(Read::Unread);
        };
        let member = self.name_at(selected);
        let unknown = LoweringRefusal::UnknownMember {
            span: selected.span,
            module: name,
            member,
        };
        if deeper.0 {
            return Err(unknown);
        }
        let Some(stated) = self
            .collected
            .structures
            .get(usize::from(parameter))
            .and_then(|structure| structure.types.iter().find(|stated| stated.name == member))
            .copied()
        else {
            return Err(unknown);
        };
        self.stated_type(site, stated)?;

        Ok(Read::Planned)
    }

    /// Build the renaming of every application written before `before` that
    /// has none yet, in source order.
    ///
    /// # Specification
    /// - requires: every type an argument or a functor's body writes before
    ///   `before` is minted.
    /// - ensures: each application whose form starts before `before` has its
    ///   renaming, or the refusal of an argument type that did not lower, and
    ///   the type of each manifest component its instance exports; the
    ///   applications are taken in source order, so an instance applied to an
    ///   earlier instance reads that instance's types.
    /// - provides: the renamings the mint sweep's instance types and
    ///   [`Self::mint_instances`] read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an instance applied to a sealed argument reads the
    ///   argument's atom, and one applied to an instance reads that instance's
    ///   type.
    /// - witness: `modules::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `modules::modules::functors::an_instance_can_be_an_argument`
    #[spec(
        captures: before_count = self.renamings.len(),
        ensures: self.renamings.len() >= before_count && self.renamings.len() <= self.collected.instances.len(),
    )]
    pub(super) fn rename_instances_before(
        &mut self,
        before: Maybe<ByteOffset, renamed_through::Absent>,
        sink: &mut Sink<'_>,
    )
    {
        while let Some(instance) = self.collected.instances.get(self.renamings.len()) {
            if let Maybe::Present(offset) = before
                && instance.declared_by.span.start() >= offset
            {
                return;
            }
            let index = InstanceIndex(self.renamings.len());
            let renaming = self.instance_renaming(index, sink);
            self.renamings.push(renaming);
            self.instance_manifests(index, sink);
        }
    }

    /// The renaming the application at `index` reads its template through.
    ///
    /// # Specification
    /// - requires: every earlier application is renamed.
    /// - ensures: each body slot's constant renamed to its image's, each body
    ///   atom to its image's atom, each parameter value component to its
    ///   witness and each parameter atom to the argument's type; the refusal of
    ///   the argument's type component when that type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::rename_instances_before`].
    /// - witness: `modules::modules::functors::the_classic_functor_pair_checks`
    #[spec(ensures: |ret| ret.is_ok() || self.collected.instances.get(usize::from(index)).is_some())]
    fn instance_renaming(
        &self,
        index: InstanceIndex,
        sink: &mut Sink<'_>,
    ) -> Result<Renaming, LoweringRefusal<'source>>
    {
        let mut renaming = Renaming::new();
        let Some(instance) = self.collected.instances.get(usize::from(index))
        else {
            return Ok(renaming);
        };
        let Some(functor) = self.collected.functors.get(usize::from(instance.functor))
        else {
            return Ok(renaming);
        };
        let Maybe::Present(origin) = self.origin_at(instance.declared_by.node)
        else {
            return Ok(renaming);
        };
        for template in usize::from(functor.body_first) .. usize::from(functor.end) {
            let (Some(slot), Maybe::Present(image)) = (
                self.collected.slots.get(template),
                instance.image(functor, SlotIndex::from(template)),
            )
            else {
                continue;
            };
            let Some(mirror) = self.collected.slots.get(usize::from(image))
            else {
                continue;
            };
            renaming.constant(slot.constant, mirror.constant);
            if slot.role == Role::Abstract {
                let atom = sink.arena.value_type_abstract(mirror.constant);
                sink.origins.record_value_type(atom, origin);
                renaming.atom(slot.constant, atom);
            }
        }
        for &matched in &instance.matched {
            match matched {
                | Matched::Value {
                    parameter, witness, ..
                } => {
                    if let (Some(stand_in), Some(checked)) = (
                        self.collected.slots.get(usize::from(parameter)),
                        self.collected.slots.get(usize::from(witness)),
                    ) {
                        renaming.constant(stand_in.constant, checked.constant);
                    }
                },
                | Matched::Abstract {
                    parameter,
                    argument,
                    ..
                } => {
                    let read = self.argument_type(argument, sink, origin)?;
                    if let Some(stand_in) = self.collected.slots.get(usize::from(parameter)) {
                        renaming.atom(stand_in.constant, read);
                    }
                },
                | Matched::Manifest { .. } => {},
            }
        }

        Ok(renaming)
    }

    /// The type the argument's type component `argument` reads.
    ///
    /// # Specification
    /// - requires: the argument's types are minted and every earlier
    ///   application is renamed.
    /// - ensures: the type a manifest component lowered to, the atom a sealed
    ///   one's abstract slot declares, recorded at `origin`, or the type an
    ///   earlier instance's manifest component reads.
    /// - fails: the refusal the component's slot holds;
    ///   [`LoweringRefusal::UnresolvedTypeHead`] naming the component when its
    ///   type is a family or did not lower and its slot holds none.
    /// - panics: none.
    ///
    /// # Errors
    /// The refusal of the component's slot.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::rename_instances_before`].
    /// - witness: `modules::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `modules::modules::functors::an_instance_can_be_an_argument`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value_type(id).is_some()))]
    fn argument_type(
        &self,
        argument: TypeComponent<'source>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<ValueTypeId, LoweringRefusal<'source>>
    {
        let unlowered = || {
            self.collected
                .slots
                .get(usize::from(argument.held))
                .map_or_else(
                    || LoweringRefusal::UnresolvedTypeHead {
                        span: origin.span(),
                        name: argument.name,
                        arity: crate::resolve::HeadArity::Nullary,
                    },
                    |held| match held.refusal {
                        | Maybe::Present((_, refusal)) => refusal,
                        | Maybe::Absent(_) => LoweringRefusal::UnresolvedTypeHead {
                            span: held.named.span,
                            name: argument.name,
                            arity: crate::resolve::HeadArity::Nullary,
                        },
                    },
                )
        };
        match argument.meaning {
            | TypeMeaning::Manifest(defined) => match self.value_type_at(defined.node) {
                | Maybe::Present(id) => Ok(id),
                | Maybe::Absent(_) => Err(unlowered()),
            },
            | TypeMeaning::Sealed => {
                let Some(atom) = self.collected.slots.get(usize::from(argument.held))
                else {
                    return Err(unlowered());
                };
                if let Maybe::Present((_, refusal)) = atom.refusal {
                    return Err(refusal);
                }
                let id = sink.arena.value_type_abstract(atom.constant);
                sink.origins.record_value_type(id, origin);
                Ok(id)
            },
            | TypeMeaning::Instantiated { defined, instance } => self
                .instance_types
                .get(&(instance, defined.node))
                .copied()
                .ok_or_else(unlowered),
            | TypeMeaning::Family(_) => Err(unlowered()),
        }
    }

    /// Mint the type each manifest component of the instance at `index`
    /// reads: its template's type, renamed.
    ///
    /// # Specification
    /// - requires: the instance's renaming is built.
    /// - ensures: every manifest component of every module of the instance
    ///   whose template's type lowered has its renamed type recorded, every
    ///   node the renaming minted carrying the origin of the node it was
    ///   renamed from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a transparent functor's manifest result reads the
    ///   argument's type at each instance.
    /// - witness: `modules::modules::functors::a_transparent_result_reads_the_argument_through`
    #[spec(
        captures: before = self.instance_types.len(),
        ensures: self.instance_types.len() >= before,
    )]
    fn instance_manifests(
        &mut self,
        index: InstanceIndex,
        sink: &mut Sink<'_>,
    )
    {
        let Some(instance) = self.collected.instances.get(usize::from(index))
        else {
            return;
        };
        let Maybe::Present(origin) = self.origin_at(instance.declared_by.node)
        else {
            return;
        };
        let mut written = Vec::new();
        for &image in instance.images.values() {
            if let Some(structure) = self.collected.structures.get(usize::from(image)) {
                for stated in structure.types.iter().chain(&structure.type_members) {
                    if let TypeMeaning::Instantiated { defined, instance } = stated.meaning
                        && instance == index
                    {
                        written.push(defined);
                    }
                }
            }
        }
        let Some(Ok(renaming)) = self.renamings.get(usize::from(index)).cloned()
        else {
            return;
        };
        for defined in written {
            if self.instance_types.contains_key(&(index, defined.node)) {
                continue;
            }
            let Maybe::Present(template) = self.value_type_at(defined.node)
            else {
                continue;
            };
            let renamed = rename_type(sink, &renaming, template, origin);
            let _fresh = self.instance_types.insert((index, defined.node), renamed);
        }
    }

    /// Lower every application's witnesses and its body's image.
    ///
    /// # Specification
    /// - requires: every template slot's own declaration is minted, and every
    ///   application is renamed.
    /// - ensures: each witness of a value component is the argument's member
    ///   checked at the parameter's type, renamed; each witness of an abstract
    ///   component the argument type's code checked at the parameter's kind,
    ///   renamed, or the fuss-free universe when none is written; each witness
    ///   of a manifest one the identity on the argument's type checked at the
    ///   function from it to the parameter's type, renamed; each image slot is
    ///   its template's declaration renamed, an abstract one sealed at the
    ///   image of its template's module. A template slot that refused is
    ///   reported once, at the template, so its image declares nothing; an
    ///   application whose argument's type did not lower, which the argument
    ///   reports, declares nothing at all.
    /// - provides: the declarations [`Self::assemble`] reads for an instance.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two applications of a counter functor yield two
    ///   abstract types at two sites, and their members each typed at its own.
    /// - witness: `modules::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `modules::modules::functors::two_applications_mint_distinct_atoms`
    #[spec(
        captures: before = self.instantiated.len(),
        ensures: self.instantiated.len() >= before,
    )]
    pub(super) fn mint_instances(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for position in 0 .. self.collected.instances.len() {
            let Some(instance) = self.collected.instances.get(position).cloned()
            else {
                continue;
            };
            let Some(template) = self
                .collected
                .functors
                .get(usize::from(instance.functor))
                .cloned()
            else {
                continue;
            };
            let functor = &template;
            let Maybe::Present(origin) = self.origin_at(instance.declared_by.node)
            else {
                continue;
            };
            let Some(Ok(renaming)) = self.renamings.get(position).map(Result::as_ref)
            else {
                continue;
            };
            let renaming = renaming.clone();
            let mut outcomes = Vec::new();
            for (component, &matched) in functor.components.iter().zip(&instance.matched) {
                let checked =
                    self.witness_outcome(component.form, matched, &renaming, sink, origin);
                let witness = match matched {
                    | Matched::Value { witness, .. }
                    | Matched::Abstract { witness, .. }
                    | Matched::Manifest { witness, .. } => witness,
                };
                if let Maybe::Present(outcome) = checked {
                    outcomes.push((witness, outcome));
                }
            }
            for template in usize::from(functor.body_first) .. usize::from(functor.end) {
                let (Some(slot), Maybe::Present(image)) = (
                    self.collected.slots.get(template),
                    instance.image(functor, SlotIndex::from(template)),
                )
                else {
                    continue;
                };
                let Maybe::Present(own) = self.own_outcome(SlotIndex::from(template), slot)
                else {
                    continue;
                };
                let renamed = match own {
                    | DeclarationOutcome::Refused(_) | DeclarationOutcome::Data(_) => continue,
                    | DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    } => DeclarationOutcome::Completed {
                        declared_type: rename_type(sink, &renaming, declared_type, origin),
                        body: rename_value(sink, &renaming, body, origin),
                    },
                    | DeclarationOutcome::Uncompleted { declared_type } => {
                        DeclarationOutcome::Uncompleted {
                            declared_type: rename_type(sink, &renaming, declared_type, origin),
                        }
                    },
                    | DeclarationOutcome::Bodied { body } => DeclarationOutcome::Bodied {
                        body: rename_value(sink, &renaming, body, origin),
                    },
                    | DeclarationOutcome::Abstract(sealing) => {
                        DeclarationOutcome::Abstract(Sealing {
                            kind: rename_type(sink, &renaming, sealing.kind, origin),
                            representation: rename_type(
                                sink,
                                &renaming,
                                sealing.representation,
                                origin,
                            ),
                            extent: sealing.extent,
                            sealing: instance
                                .images
                                .get(&sealing.sealing)
                                .copied()
                                .unwrap_or(instance.structure),
                            component: sealing.component,
                        })
                    },
                };
                outcomes.push((image, renamed));
            }
            for (slot, outcome) in outcomes {
                let _first = self.instantiated.insert(slot, outcome);
            }
        }
    }

    /// The declaration the witness `matched` checks the argument by, for a
    /// parameter component of form `form`, under `renaming`.
    ///
    /// # Specification
    /// - requires: the template's parameter types are minted.
    /// - ensures: as [`Self::mint_instances`] for one witness; absent when the
    ///   parameter's own type or kind did not lower, which its slot's refusal
    ///   reports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_instances`].
    /// - witness: `modules::modules::functors::an_argument_is_matched_against_the_parameter`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(DeclarationOutcome::Completed { .. })))]
    fn witness_outcome(
        &self,
        form: ParameterForm,
        matched: Matched<'source>,
        renaming: &Renaming,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        match (form, matched) {
            | (ParameterForm::Value(typed), Matched::Value { member, .. }) => {
                let (Maybe::Present(stated), Some(read)) = (
                    self.value_type_at(typed.node),
                    self.collected.slots.get(usize::from(member)),
                )
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let declared_type = rename_type(sink, renaming, stated, origin);
                let body = sink.arena.value_constant(read.constant);
                sink.origins.record_value(body, origin);
                Maybe::Present(DeclarationOutcome::Completed {
                    declared_type,
                    body,
                })
            },
            | (ParameterForm::Abstract(kind), Matched::Abstract { argument, .. }) => {
                let Ok(read) = self.argument_type(argument, sink, origin)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let declared_type = match kind {
                    | Maybe::Present(written) => match self.value_type_at(written.node) {
                        | Maybe::Present(stated) => rename_type(sink, renaming, stated, origin),
                        | Maybe::Absent(reason) => return Maybe::Absent(reason),
                    },
                    | Maybe::Absent(_) => {
                        let id = sink.arena.value_type_universe(
                            Sort::Ground(Universe::FUSS_FREE.sort),
                            Level::constant(Universe::FUSS_FREE.level),
                        );
                        sink.origins.record_value_type(id, origin);
                        id
                    },
                };
                let body = sink.arena.value_quote(read);
                sink.origins.record_value(body, origin);
                Maybe::Present(DeclarationOutcome::Completed {
                    declared_type,
                    body,
                })
            },
            | (ParameterForm::Manifest(defined), Matched::Manifest { argument, .. }) => {
                let (Ok(read), Maybe::Present(stated)) = (
                    self.argument_type(argument, sink, origin),
                    self.value_type_at(defined.node),
                )
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let expected = rename_type(sink, renaming, stated, origin);
                let returner = sink.arena.comp_type_returner(expected);
                sink.origins.record_comp_type(returner, origin);
                let arrow = sink.arena.comp_type_arrow(read, returner);
                sink.origins.record_comp_type(arrow, origin);
                let declared_type = sink.arena.value_type_thunk(arrow);
                sink.origins.record_value_type(declared_type, origin);
                let bound = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(bound, origin);
                let returned = sink.arena.computation_return(bound);
                sink.origins.record_computation(returned, origin);
                let lambda = sink.arena.computation_lambda(returned);
                sink.origins.record_computation(lambda, origin);
                let body = sink.arena.value_thunk(lambda);
                sink.origins.record_value(body, origin);
                Maybe::Present(DeclarationOutcome::Completed {
                    declared_type,
                    body,
                })
            },
            | (
                ParameterForm::Value(_) | ParameterForm::Abstract(_) | ParameterForm::Manifest(_),
                Matched::Value { .. } | Matched::Abstract { .. } | Matched::Manifest { .. },
            ) => Maybe::Absent(lowered::Absent::Unminted),
        }
    }
}

/// Whether a path's parameter half planned the path.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Read
{
    /// The head names no parameter here: the outermost scope reads the path.
    Unread,
    /// The path is planned as a parameter's component.
    Planned,
}

/// Whether a path selects past its first link.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Deeper(pub bool);

quenchant_shape::reason_enum! {
    /// Why a path head names no functor parameter.
    pub(super) mod parameter_path {
        /// The path is not read inside a functor of that parameter.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No enclosing functor's parameter bears the head's name.
            Outside,
        }
    }
}

/// `subject` renamed by `renaming`, every node the renaming minted carrying
/// the origin of the node it was renamed from, or `fallback`.
///
/// # Specification
/// - requires: `subject` is a value type of `sink`'s arena.
/// - ensures: as [`rename_value_type_traced`], with every minted node's origin
///   recorded.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::mint_instances`].
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[spec(ensures: |ret| ret == subject || sink.arena.value_type(ret).is_some())]
fn rename_type(
    sink: &mut Sink<'_>,
    renaming: &Renaming,
    subject: ValueTypeId,
    fallback: Origin,
) -> ValueTypeId
{
    let mark = sink.arena.watermark();
    let mut carried: Vec<Carried> = Vec::new();
    let renamed = rename_value_type_traced(sink.arena, subject, renaming, &mut carried);
    record_copies(sink, mark, &carried, fallback);
    renamed
}

/// `subject` renamed by `renaming`, every node the renaming minted carrying
/// the origin of the node it was renamed from, or `fallback`.
///
/// # Specification
/// - requires: `subject` is a value of `sink`'s arena.
/// - ensures: as [`rename_value_traced`], with every minted node's origin
///   recorded.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::mint_instances`].
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[spec(ensures: |ret| ret == subject || sink.arena.value(ret).is_some())]
fn rename_value(
    sink: &mut Sink<'_>,
    renaming: &Renaming,
    subject: ValueId,
    fallback: Origin,
) -> ValueId
{
    let mark = sink.arena.watermark();
    let mut carried: Vec<Carried> = Vec::new();
    let renamed = rename_value_traced(sink.arena, subject, renaming, &mut carried);
    record_copies(sink, mark, &carried, fallback);
    renamed
}

quenchant_shape::reason_enum! {
    /// Why a renaming pass names no source offset to stop before.
    pub(super) mod renamed_through {
        /// The pass renames every application.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every application is renamed, however late it is written.
            Everything,
        }
    }
}
