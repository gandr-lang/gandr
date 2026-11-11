//! The lowering half of a path: each body minted as a function between packed
//! models, and each round trip as a definition over the bound model. The
//! design lives with the collection pass (`crate::module::path`).
//!
//! # A body is its template read over the bound model
//!
//! A body's template reads each member of its domain as a parameter slot's
//! constant, and each sort as its atom. The function binds the model `s`,
//! then each sort and value member of `s` in signature order, `x ← s.m`, and
//! returns the codomain's record of the body's members, read over those
//! variables: a constant as its variable, an atom as its code's decode. A
//! member that is a domain member's name alone is that member's variable, so
//! a renaming costs a projection and no other node.
//!
//! # A round trip is a reflexivity over the bound model
//!
//! The round trip of a member `m` of `V1` states `(s : Model(V1)) -> Path(
//! p.from(p.into(s)).m, s.m)`, each endpoint the value its computation returns,
//! and its body is `Path.here(s.m)`. The checker reads the body against the
//! type, so conversion decides the round trip over the variable `s`, and an
//! endpoint the point does not convert to is refused at the member the second
//! body defines.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::Renaming;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::abstract_constant_value_traced;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::Lowered;
use super::Lowerer;
use super::Reading;
use super::Sink;
use super::Site;
use super::arity;
use super::exits::record_copies;
use super::functor::rename_type;
use super::functor::rename_value;
use super::model::Bundled;
use super::model::packed_record;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::form::Placed;
use crate::form::Universe;
use crate::model::ModelComponent;
use crate::model::ModelForm;
use crate::model::ModelSignature;
use crate::module::BodyScope;
use crate::module::ComponentPlace;
use crate::module::Container;
use crate::module::DeclarationOutcome;
use crate::module::Functor;
use crate::module::FunctorIndex;
use crate::module::ParameterForm;
use crate::module::PathDeclaration;
use crate::module::Role;
use crate::module::RoundTrip;
use crate::module::Side;
use crate::module::SlotIndex;
use crate::module::TypeMeaning;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;

/// The model a body binds and the model it packs: each signature's bundle and
/// the type it mints to.
///
/// # Specification
/// trivial.
struct Ends
{
    /// The domain's bundle.
    domain: Bundled,
    /// The domain's model type.
    domain_type: ValueTypeId,
    /// The codomain's bundle.
    codomain: Bundled,
    /// The codomain's model type.
    codomain_type: ValueTypeId,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Mint every path the source being lowered declares: its two functions
    /// and its round trips.
    ///
    /// # Specification
    /// - requires: every template slot of the source is lowered.
    /// - ensures: each function and each round trip of a path the source
    ///   declares holds the declaration [`Self::path_function`] or
    ///   [`Self::round_trip`] mints for it.
    /// - provides: the declarations [`Self::outcome`] reads for a path.
    /// - fails: never; a refusal is the declaration's own.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each function and each round trip of a path is a
    ///   completed declaration.
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    #[spec(
        captures: before = self.pathed.len(),
        ensures: self.pathed.len() >= before,
    )]
    pub(super) fn mint_paths(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let source = self.current.source;
        let paths: Vec<PathDeclaration<'source>> = self
            .collected
            .paths
            .iter()
            .filter(|path| self.collected.unit.source_at(path.declared_by.span.start()) == source)
            .cloned()
            .collect();
        for path in &paths {
            for side in [Side::Into, Side::From] {
                let (functor, slot) = path.body(side);
                let outcome = self.path_function(path, functor, sink);
                let _first = self.pathed.insert(slot, outcome);
            }
            for trip in &path.trips {
                let outcome = self.round_trip(path, trip, sink);
                let _first = self.pathed.insert(trip.slot, outcome);
            }
        }
    }

    /// The bundles and the model types of the two signatures the body
    /// `template` maps between.
    ///
    /// # Specification
    /// - requires: `template` is a path's body.
    /// - ensures: each signature's bundle as [`Self::theory_bundle`] reads it
    ///   and the type [`Self::mint_bundle_fixed`] mints for it, with no sort
    ///   fixed; the unminted refusal at the body's keyword when a type does not
    ///   mint.
    /// - fails: as [`Self::theory_bundle`].
    /// - panics: none.
    ///
    /// # Errors
    /// The refusal of a signature that bundles no model type.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_paths`].
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|_| true, |ends| sink.arena.value_type(ends.domain_type).is_some() && sink.arena.value_type(ends.codomain_type).is_some()))]
    fn path_ends(
        &self,
        template: &Functor<'source>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<Ends, LoweringRefusal<'source>>
    {
        let unminted = LoweringRefusal::Unminted {
            span: template.named.span,
            name: template.name,
        };
        let BodyScope::Path {
            ref domain,
            ref codomain,
        } = template.scope
        else {
            return Err(unminted);
        };
        let site = |at: Placed| Site {
            at,
            name: FormName::PATH,
            reading: Reading::ValueType(Frame::Outermost),
        };
        let domain_bundle = self.theory_bundle(site(domain.named), domain)?;
        let codomain_bundle = self.theory_bundle(site(codomain.named), codomain)?;
        let (
            Maybe::Present(Lowered::ValueType(domain_type)),
            Maybe::Present(Lowered::ValueType(codomain_type)),
        ) = (
            self.mint_bundle_fixed(&domain_bundle, &[], sink, origin),
            self.mint_bundle_fixed(&codomain_bundle, &[], sink, origin),
        )
        else {
            return Err(unminted);
        };

        Ok(Ends {
            domain: domain_bundle,
            domain_type,
            codomain: codomain_bundle,
            codomain_type,
        })
    }

    /// The members of its domain `domain` the body `template` reads, in
    /// signature order: each sort and each value member.
    ///
    /// # Specification
    /// trivial.
    fn read_members(
        &self,
        template: &Functor<'source>,
        domain: &ModelSignature,
    ) -> Vec<Read>
    {
        let places: BTreeMap<&str, ComponentPlace> = domain
            .components
            .iter()
            .enumerate()
            .map(|(place, member)| (member.name.as_ref(), ComponentPlace(place)))
            .collect();
        let mut read: Vec<Read> = template
            .components
            .iter()
            .filter_map(|component| {
                let constant = self
                    .collected
                    .slots
                    .get(usize::from(component.slot))?
                    .constant;
                match component.form {
                    ParameterForm::Derived(part) => Some(Read {
                        place: part.component,
                        constant,
                        sort: false,
                    }),
                    ParameterForm::Abstract(_) => {
                        let name: &str = component.name.as_ref();
                        places.get(name).map(|&place| Read {
                            place,
                            constant,
                            sort: true,
                        })
                    },
                    ParameterForm::Value(_) | ParameterForm::Manifest(_) => None,
                }
            })
            .collect();
        read.sort_unstable_by_key(|member| member.place);
        read
    }

    /// The function the body `functor` of a path lowers to: from its domain's
    /// models to its codomain's.
    ///
    /// # Specification
    /// - requires: the body's template slots are lowered.
    /// - ensures: the thunk of a lambda over the domain's model `s`, which
    ///   binds each sort and each value member of `s` the body reads, in
    ///   signature order, and returns the codomain's record of the body's
    ///   members, each read over those variables: a domain sort as the decode
    ///   of its code's variable and a domain member's constant as its variable;
    ///   a codomain sort is the code of the type the body states for it, the
    ///   code itself when that type decodes one. The function is typed `+U
    ///   (Model(V1) -> -F Model(V2))`. A body member a template slot refused is
    ///   that refusal; a codomain component the body does not define, and a
    ///   sort with indices or of computations on either side, is refused
    ///   unminted at the body's keyword.
    /// - fails: never; a refusal is the declaration's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_paths`], and a body that moves a sort
    ///   binds its code.
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    /// - witness: `tests::modules::paths::a_path_that_moves_a_sort_states_its_round_trip_3487`
    #[spec(ensures: |ret| matches!(ret, DeclarationOutcome::Completed { .. } | DeclarationOutcome::Refused(_)))]
    fn path_function(
        &self,
        path: &PathDeclaration<'source>,
        functor: FunctorIndex,
        sink: &mut Sink<'_>,
    ) -> DeclarationOutcome<'source>
    {
        let Some(template) = self.collected.functors.get(usize::from(functor))
        else {
            return DeclarationOutcome::Refused(LoweringRefusal::Unminted {
                span: path.declared_by.span,
                name: path.name,
            });
        };
        let unminted = DeclarationOutcome::Refused(LoweringRefusal::Unminted {
            span: template.named.span,
            name: template.name,
        });
        let Maybe::Present(origin) = self.origin_at(template.named.node)
        else {
            return unminted;
        };
        let ends = match self.path_ends(template, sink, origin) {
            Ok(ends) => ends,
            Err(refusal) => return DeclarationOutcome::Refused(refusal),
        };
        let (Some(domain), Some(codomain)) = (ends.domain.outermost(), ends.codomain.outermost())
        else {
            return unminted;
        };
        if domain
            .components
            .iter()
            .chain(&codomain.components)
            .any(|component| {
                moved_sort(component).is_none()
                    && matches!(component.form, Ok(ModelForm::Sort { .. }))
            })
        {
            return unminted;
        }
        let read = self.read_members(template, domain);
        let bound: Vec<Read> = read.iter().copied().filter(|member| !member.sort).collect();
        let count = bound.len();
        // A sort is read off `s` where the record stands, past the value
        // members bound before it, so its code stays the projection the
        // checker reads `s`'s fields by.
        let Some(sorts) = decoded_sorts(&read, sink, origin, |sink, place| {
            let held = bound_model(sink, ComponentCount::from(count), origin);
            Self::sort_code(&ends.domain, domain, (held, place), sink, origin)
        })
        else {
            return unminted;
        };
        let mut values = Vec::with_capacity(codomain.components.len());
        let mut carried = Vec::new();
        for component in &codomain.components {
            let written = if moved_sort(component).is_some() {
                match self.body_sort(template, &component.name, &sorts, sink, origin) {
                    Some(code) => code,
                    None => return unminted,
                }
            }
            else {
                let Some((position, slot)) = self.body_member(template, &component.name)
                else {
                    return unminted;
                };
                match self.own_outcome(position, slot) {
                    Maybe::Present(DeclarationOutcome::Completed { body, .. }) => {
                        rename_value(sink, &sorts, body, origin)
                    },
                    Maybe::Present(DeclarationOutcome::Refused(refusal)) => {
                        return DeclarationOutcome::Refused(refusal);
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => return unminted,
                }
            };
            let mut value = written;
            for (position, member) in bound.iter().enumerate() {
                let index = de_bruijn(ComponentCount::from(
                    count.saturating_sub(position).saturating_sub(1),
                ));
                let mark = sink.arena.watermark();
                carried.clear();
                value = abstract_constant_value_traced(
                    sink.arena,
                    value,
                    (member.constant, index),
                    &mut carried,
                );
                record_copies(sink, mark, &carried, origin);
            }
            values.push(value);
        }
        let below = origin.inserted(Insertion::Model);
        let Some(record) = packed_record(codomain, &values, sink, (origin, below))
        else {
            return unminted;
        };
        let mut body = sink.arena.computation_return(record);
        sink.origins.record_computation(body, origin);
        for (position, member) in bound.iter().enumerate().rev() {
            let held = bound_model(sink, ComponentCount::from(position), origin);
            let Maybe::Present(projected) =
                Self::member_of(&ends.domain, domain, (held, member.place), sink, origin)
            else {
                return unminted;
            };
            body = sink.arena.computation_bind(projected, body);
            sink.origins.record_computation(body, origin);
        }
        let lambda = sink.arena.computation_lambda(body);
        sink.origins.record_computation(lambda, origin);
        let thunk = sink.arena.value_thunk(lambda);
        sink.origins.record_value(thunk, origin);
        let returner = sink.arena.comp_type_returner(ends.codomain_type);
        sink.origins.record_comp_type(returner, origin);
        let arrow = sink.arena.comp_type_arrow(ends.domain_type, returner);
        sink.origins.record_comp_type(arrow, origin);
        let declared_type = sink.arena.value_type_thunk(arrow);
        sink.origins.record_value_type(declared_type, origin);

        DeclarationOutcome::Completed {
            declared_type,
            body: thunk,
        }
    }

    /// The code of the type the body `template` states for its sort `name`,
    /// each domain sort read as `sorts` reads it.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, and each type `sorts` names is read
    ///   where the body's record stands.
    /// - ensures: the code a decode reads when the stated type is one, and the
    ///   quote of the stated type otherwise; nothing when the body states no
    ///   type of that name, or its type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::path_function`].
    /// - witness: `tests::modules::paths::a_path_that_moves_a_sort_states_its_round_trip_3487`
    #[spec(ensures: |ret| ret.is_none_or(|id| sink.arena.value(id).is_some()))]
    fn body_sort(
        &self,
        template: &Functor<'source>,
        name: &Name,
        sorts: &Renaming,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Option<ValueId>
    {
        let name: &str = name.as_ref();
        let stated = self
            .collected
            .structures
            .get(usize::from(template.body))?
            .types
            .iter()
            .find(|component| component.name.as_ref() == name)?;
        let TypeMeaning::Manifest(defined) = stated.meaning
        else {
            return None;
        };
        let Maybe::Present(written) = self.value_type_at(defined.node)
        else {
            return None;
        };
        let read = rename_type(sink, sorts, written, origin);
        if let Some(&ValueType::Element { code, .. }) = sink.arena.value_type(read) {
            return Some(code);
        }
        let quoted = sink.arena.value_quote(read);
        sink.origins
            .record_value(quoted, origin.inserted(Insertion::Quote));

        Some(quoted)
    }

    /// The round trip `trip` of the path `path`: its member brought back
    /// through both bodies is the member.
    ///
    /// # Specification
    /// - requires: the path's two functions are minted, as
    ///   [`Self::path_function`] mints them.
    /// - ensures: the thunk of a lambda over the member's model `s` returning
    ///   `Path.here(s.m)`, typed `+U ((s : Model(V)) -> -F Path[.A = T](
    ///   second(first(s)).m, s.m))`, each endpoint the value its computation
    ///   returns, `first` the body from the member's signature and `second` the
    ///   one back. `T` is the universe for a sort, and for a value member the
    ///   type the derivation states for it, each sort read as the decode of its
    ///   code off `s`. A type that does not mint is refused unminted at the
    ///   witness. Each node is located at the member that the body defines, or
    ///   at the theory's member for `s.m`, as [`Insertion::Relation`]: the
    ///   source writes the path's bodies, never its round trips, so no hover
    ///   answers with the term or the type of a trip.
    /// - fails: never; a refusal is the declaration's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_paths`].
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    #[spec(ensures: |ret| matches!(ret, DeclarationOutcome::Completed { .. } | DeclarationOutcome::Refused(_)))]
    fn round_trip(
        &self,
        path: &PathDeclaration<'source>,
        trip: &RoundTrip<'source>,
        sink: &mut Sink<'_>,
    ) -> DeclarationOutcome<'source>
    {
        let (first, second) = match trip.side {
            Side::From => (path.into, path.from),
            Side::Into => (path.from, path.into),
        };
        let Some(witness) = self.collected.slots.get(usize::from(trip.slot))
        else {
            return DeclarationOutcome::Refused(LoweringRefusal::Unminted {
                span: path.declared_by.span,
                name: trip.name,
            });
        };
        let unminted = DeclarationOutcome::Refused(LoweringRefusal::Unminted {
            span: witness.introduced_by.span,
            name: trip.name,
        });
        let (Maybe::Present(origin), Some(template)) = (
            self.origin_at(witness.introduced_by.node),
            self.collected.functors.get(usize::from(first.0)),
        )
        else {
            return unminted;
        };
        let origin = origin.inserted(Insertion::Relation);
        let ends = match self.path_ends(template, sink, origin) {
            Ok(ends) => ends,
            Err(refusal) => return DeclarationOutcome::Refused(refusal),
        };
        let Some(signature) = ends.domain.outermost()
        else {
            return unminted;
        };
        let carrier = if signature
            .components
            .get(usize::from(trip.component))
            .and_then(moved_sort)
            .is_some()
        {
            let universe = sink.arena.value_type_universe(
                Sort::Ground(GroundSort::Value),
                Level::constant(Universe::FUSS_FREE.level),
            );
            sink.origins.record_value_type(universe, origin);
            universe
        }
        else {
            let Some(stated) = self.trip_carrier(template, trip.component)
            else {
                return unminted;
            };
            let read = self.read_members(template, signature);
            let Some(sorts) = decoded_sorts(&read, sink, origin, |sink, place| {
                let held = bound_model(sink, ComponentCount::default(), origin);
                Self::sort_code(&ends.domain, signature, (held, place), sink, origin)
            })
            else {
                return unminted;
            };
            rename_type(sink, &sorts, stated, origin)
        };
        let constant = |slot: SlotIndex| {
            self.collected
                .slots
                .get(usize::from(slot))
                .map(|entry| entry.constant)
        };
        let (Some(there), Some(back)) = (constant(first.1), constant(second.1))
        else {
            return unminted;
        };
        let applied = |sink: &mut Sink<'_>, function: ConstantIndex| {
            let head = sink.arena.value_constant(function);
            sink.origins.record_value(head, origin);
            let forced = sink.arena.computation_force(head);
            sink.origins.record_computation(forced, origin);
            let argument = bound_model(sink, ComponentCount::default(), origin);
            let call = sink.arena.computation_application(forced, argument);
            sink.origins.record_computation(call, origin);
            call
        };
        // `second(first(s))`, the model there and back, held as the value its
        // computation returns: a bind of the member read off it would state a
        // type that names the model it binds.
        let back_call = applied(sink, back);
        let there_call = applied(sink, there);
        let round = sink.arena.computation_bind(there_call, back_call);
        sink.origins.record_computation(round, origin);
        let brought = sink.arena.value_returned(round);
        sink.origins
            .record_value(brought, origin.inserted(Insertion::Endpoint));
        let Maybe::Present(read) = Self::member_of(
            &ends.domain,
            signature,
            (brought, trip.component),
            sink,
            origin,
        )
        else {
            return unminted;
        };
        let left = sink.arena.value_returned(read);
        sink.origins.record_value(left, origin);
        // `s.m`, placed at the member the theory states, so a refusal marks
        // both the body's definition and the member it must come back to.
        let stated_at = match signature
            .components
            .get(usize::from(trip.component))
            .map(|member| self.origin_at(member.named.node))
        {
            Some(Maybe::Present(at)) => at.inserted(Insertion::Relation),
            Some(Maybe::Absent(_)) | None => origin,
        };
        let own_model = bound_model(sink, ComponentCount::default(), stated_at);
        let Maybe::Present(own) = Self::member_of(
            &ends.domain,
            signature,
            (own_model, trip.component),
            sink,
            stated_at,
        )
        else {
            return unminted;
        };
        let right = sink.arena.value_returned(own);
        sink.origins.record_value(right, stated_at);
        let stated = sink.arena.value_type_path(carrier, left, right);
        sink.origins.record_value_type(stated, origin);
        let returner = sink.arena.comp_type_returner(stated);
        sink.origins.record_comp_type(returner, origin);
        let pi = sink.arena.comp_type_pi(ends.domain_type, returner);
        sink.origins.record_comp_type(pi, origin);
        let declared_type = sink.arena.value_type_thunk(pi);
        sink.origins.record_value_type(declared_type, origin);
        let point_model = bound_model(sink, ComponentCount::default(), origin);
        let Maybe::Present(point) = Self::member_of(
            &ends.domain,
            signature,
            (point_model, trip.component),
            sink,
            origin,
        )
        else {
            return unminted;
        };
        let returned = sink.arena.value_returned(point);
        sink.origins.record_value(returned, origin);
        let here = sink.arena.value_here(returned);
        sink.origins.record_value(here, origin);
        let done = sink.arena.computation_return(here);
        sink.origins.record_computation(done, origin);
        let lambda = sink.arena.computation_lambda(done);
        sink.origins.record_computation(lambda, origin);
        let body = sink.arena.value_thunk(lambda);
        sink.origins.record_value(body, origin);

        DeclarationOutcome::Completed {
            declared_type,
            body,
        }
    }

    /// The template slot of the body `template` defining the member `name`.
    ///
    /// # Specification
    /// trivial.
    fn body_member(
        &self,
        template: &Functor<'source>,
        name: &Name,
    ) -> Option<(SlotIndex, &crate::module::DeclarationSlot<'source>)>
    {
        let name: &str = name.as_ref();
        let body = Container::Module(template.body);
        (usize::from(template.body_first) .. usize::from(template.end)).find_map(|position| {
            self.collected
                .slots
                .get(position)
                .filter(|slot| {
                    slot.container == body
                        && slot.role == Role::Declared
                        && slot.name.as_ref() == name
                })
                .map(|slot| (SlotIndex::from(position), slot))
        })
    }

    /// The type the derivation states for the value member at `component` of
    /// the domain the body `template` reads: its parameter slot's, each sort
    /// an atom of the template.
    ///
    /// # Specification
    /// trivial.
    fn trip_carrier(
        &self,
        template: &Functor<'source>,
        component: ComponentPlace,
    ) -> Option<ValueTypeId>
    {
        template
            .components
            .iter()
            .find_map(|parameter| match parameter.form {
                ParameterForm::Derived(part) if part.component == component => {
                    self.modelled.get(&parameter.slot).copied()
                },
                ParameterForm::Derived(_)
                | ParameterForm::Value(_)
                | ParameterForm::Abstract(_)
                | ParameterForm::Manifest(_) => None,
            })
    }

    /// Read the member at `component` of the model `held`, a model of the
    /// signature `signature` that `bundle` bundles.
    ///
    /// # Specification
    /// - requires: `component` is a place of `signature`, and `held` is a value
    ///   of the bundle's type.
    /// - ensures: as [`Lowerer::project`] off `held`, at the member's label
    ///   when the bundle is a record keyed by its labels.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_paths`].
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.computation(id).is_some()))]
    fn member_of(
        bundle: &Bundled,
        signature: &ModelSignature,
        (held, component): (ValueId, ComponentPlace),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, super::lowered::Absent>
    {
        let Some(member) = signature.components.get(usize::from(component))
        else {
            return Maybe::Absent(super::lowered::Absent::Unminted);
        };
        let label = (bundle.dependent() == arity::Dependent(false))
            .then(|| FieldLabel::from(alloc::string::String::from(member.name.as_ref())));
        Self::project(
            held,
            arity::Observed {
                index: usize::from(component),
                count: signature.components.len(),
            },
            label.as_ref(),
            sink,
            origin,
        )
    }

    /// The code of the sort at `place` of the model `held`: the value its
    /// projection returns, as a model binder's carrier reads it.
    ///
    /// # Specification
    /// - requires: as [`Self::member_of`].
    /// - ensures: the returned value of [`Self::member_of`]'s projection,
    ///   marked inserted; nothing when the projection does not mint.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::path_function`].
    /// - witness: `tests::modules::paths::a_path_that_moves_a_sort_states_its_round_trip_3487`
    #[spec(ensures: |ret| ret.is_none_or(|id| matches!(sink.arena.value(id), Some(&gandr_core_term::Value::Returned(_)))))]
    fn sort_code(
        bundle: &Bundled,
        signature: &ModelSignature,
        (held, place): (ValueId, ComponentPlace),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Option<ValueId>
    {
        let Maybe::Present(projected) =
            Self::member_of(bundle, signature, (held, place), sink, origin)
        else {
            return None;
        };
        let code = sink.arena.value_returned(projected);
        sink.origins
            .record_value(code, origin.inserted(Insertion::Endpoint));

        Some(code)
    }
}

/// The model the lambda of a path's function or round trip binds, read past
/// the `binders` binders of the members bound after it.
///
/// # Specification
/// trivial.
fn bound_model(
    sink: &mut Sink<'_>,
    binders: ComponentCount,
    origin: Origin,
) -> ValueId
{
    let held = sink
        .arena
        .value_variable(Zone::Intuitionistic, de_bruijn(binders));
    sink.origins.record_value(held, origin);
    held
}

/// The de Bruijn index counting `binders` binders, one per bound member.
///
/// # Specification
/// trivial.
fn de_bruijn(binders: ComponentCount) -> DeBruijnIndex
{
    DeBruijnIndex::from(u32::from(Binders::NONE.deeper_by(binders)))
}

/// A member of its domain a path's body reads: its place in the domain's
/// signature, the constant its template reads it as, and whether it is a
/// sort, whose constant is an atom.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Read
{
    /// The member's place in the domain's signature.
    place: ComponentPlace,
    /// The constant, or the atom, its template reads it as.
    constant: ConstantIndex,
    /// Whether the member is a sort.
    sort: bool,
}

/// The component `component` when it is a sort with no indices, a code of
/// value types: a sort a path moves.
///
/// # Specification
/// trivial.
fn moved_sort(component: &ModelComponent) -> Option<&ModelComponent>
{
    matches!(
        component.form,
        Ok(ModelForm::Sort { ref indices, ground: GroundSort::Value }) if indices.is_empty()
    )
    .then_some(component)
}

/// The renaming that reads each sort of `read` as the decode of its code:
/// `code` answers the code of the sort at each place of the signature.
///
/// # Specification
/// - requires: each code `code` answers is read where the renamed subject
///   stands.
/// - ensures: one atom per sort of `read`, each the decode, in the fuss-free
///   universe, of its code, marked inserted; nothing when a code is not
///   answered.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::path_function`].
/// - witness: `tests::modules::paths::a_path_that_moves_a_sort_states_its_round_trip_3487`
#[spec(ensures: |ret| ret.is_some() || read.iter().any(|member| member.sort))]
fn decoded_sorts(
    read: &[Read],
    sink: &mut Sink<'_>,
    origin: Origin,
    mut code: impl FnMut(&mut Sink<'_>, ComponentPlace) -> Option<ValueId>,
) -> Option<Renaming>
{
    let mut renaming = Renaming::new();
    for member in read.iter().filter(|member| member.sort) {
        let held = code(sink, member.place)?;
        let decoded = sink
            .arena
            .value_type_element(held, Level::constant(Universe::FUSS_FREE.level));
        sink.origins
            .record_value_type(decoded, origin.inserted(Insertion::Decode));
        renaming.atom(member.constant, decoded);
    }

    Some(renaming)
}
