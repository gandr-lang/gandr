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
//!
//! # A module packs as the record its members give
//!
//! `pack M at Model(T)` reads the module `M`, declared before it, as a value
//! of `Model(T)`: one value per component of `T`'s signature, in its order —
//! the code of the type an unindexed sort's type member states, the member
//! module of a nested component's name packed the same way, and the member
//! of the name of every other component — nested as the bundled record nests
//! its fields. The kernel checks the record at the stated type, so a member
//! whose type is not its component's is refused there. A sort the module seals
//! is out of the fragment: the record would name the representation the seal
//! hides, and a package over the abstract type carries such a module.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CertificateEquality;
use gandr_core_term::Computation;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::TermId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::ByteOffset;
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
use super::Universe;
use super::arity;
use super::closed;
use super::exhausted;
use super::exits;
use super::identity::related;
use super::lowered;
use super::stretch;
use crate::error::AscriptionForm;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::error::TelescopeFault;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::model::Binder;
use crate::model::Dependent;
use crate::model::ModelComponent;
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
use crate::module::Member;
use crate::module::ModelPart;
use crate::module::Operand;
use crate::module::SlotIndex;
use crate::module::Stratum;
use crate::module::StructureIndex;
use crate::module::TypeMeaning;
use crate::module::spine_domains;
use crate::module::ungrouped;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;
use crate::resolve::Telescope;
use crate::resolve::type_atom;

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

/// How a law's term reads a member of the model it is minted in.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MemberRead
{
    /// An operation: the member forced and applied to the term's arguments.
    Applied,
    /// A constant: the member's value itself.
    Held,
}

/// Where a derived type reads the sorts and operations it names.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Members<'source, 'model>
{
    /// The members of a module.
    Module
    {
        /// The module the type is read in.
        structure: StructureIndex,
        /// Each operation and constant of the model, by its name in the
        /// theory, with the member name it reads in the module and how a term
        /// reads it.
        operations: BTreeMap<Name, (SurfaceName<'source>, MemberRead)>,
    },
    /// The fields of a bundled model before the one being minted.
    Fields(Fields<'model>),
}

/// The fields of a bundled model a later field reads: the components before
/// it, each with whether its link binds, and the manifest sorts the bundle
/// fixes instead of holding.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Fields<'model>
{
    /// The components, in signature order.
    before: &'model [ModelComponent],
    /// Whether each one's link binds, in the same order.
    binds: &'model [Dependent],
    /// Each manifest sort's name beside the type it is, read outside the
    /// record.
    manifests: &'model [(&'model Name, ValueTypeId)],
}

impl Fields<'_>
{
    /// The index the field named `name` is read at under `context`.
    ///
    /// # Specification
    /// - requires: `context` is the telescope prefix the reading stands under,
    ///   inside the field after the last of `before`.
    /// - ensures: for the last component of the name, when its link binds, the
    ///   count of the binding links after it plus the binding binders of
    ///   `context`; nothing for a name no binding link bears.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the carrier read by the start, the step and the
    ///   reading, and an operation read by a law under its telescope.
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    /// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
    #[spec(ensures: |ret| ret.is_none() || !self.before.is_empty())]
    fn index(
        self,
        name: &Name,
        context: Context<'_>,
    ) -> Option<DeBruijnIndex>
    {
        let place = self
            .before
            .iter()
            .rposition(|component| component.name == *name)?;
        if !self.binds.get(place).is_some_and(|binds| binds.0) {
            return None;
        }
        let links = self
            .binds
            .get(place.saturating_add(1) ..)
            .unwrap_or_default()
            .iter()
            .filter(|binds| binds.0)
            .count();
        let telescope = context.dependent.iter().filter(|binds| binds.0).count();

        u32::try_from(links.saturating_add(telescope))
            .ok()
            .map(DeBruijnIndex::from)
    }

    /// The type the manifest sort `name` is, beside the binders a reading
    /// under `context` stands below the record's outside.
    ///
    /// # Specification
    /// - requires: as [`Self::index`].
    /// - ensures: for a sort the bundle fixes, its type beside the count of the
    ///   binding links before the field read plus the binding binders of
    ///   `context`; nothing for any other name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a toggle whose carrier is fixed reads it in its start
    ///   and under its step's telescope, and a fixed sort a later field binds
    ///   past.
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    /// - witness: `tests::modules::models::a_manifest_sort_reads_past_the_links_before_it`
    #[spec(ensures: |ret| ret.is_none() || !self.manifests.is_empty())]
    fn manifest(
        self,
        name: &Name,
        context: Context<'_>,
    ) -> Option<(ValueTypeId, Binders)>
    {
        let &(_, id) = self
            .manifests
            .iter()
            .find(|&&(manifest, _)| manifest == name)?;
        let links = self.binds.iter().filter(|binds| binds.0).count();
        let telescope = context.dependent.iter().filter(|binds| binds.0).count();
        let lift = u32::try_from(links.saturating_add(telescope)).ok()?;

        Some((id, Binders::from(lift)))
    }
}

/// What a derived type is minted for: where it reads what it names, and the
/// origin every node it mints carries.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Minting<'source, 'model>
{
    /// Where the type reads the sorts and operations it names.
    members: Members<'source, 'model>,
    /// The origin every minted node carries.
    origin: Origin,
}

/// A theory's models as a type: the signature of every theory its bundled
/// record reads, the outermost first, each beside the places of the theories
/// its nested components name, and the name the type is written over.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Bundled
{
    /// The theories, the outermost first; a nested theory stands after the
    /// one nesting it. The outermost holds no component its manifest sorts
    /// fix.
    theories: Vec<BundledTheory>,
    /// The theory's name, `T` in `Model(T)`, where every node below the type
    /// is located.
    named: NodeIndex,
    /// The outermost theory's manifest sorts, `with sort x = A`: each sort's
    /// name beside the type it is.
    manifests: Vec<(Name, NodeIndex)>,
}

/// One theory of a [`Bundled`] record.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct BundledTheory
{
    /// The signature the theory derives.
    signature: ModelSignature,
    /// The place of each nested component's theory, in the order the
    /// components stand.
    nested: Vec<usize>,
}

/// A module packed at its model type: the theories of the bundle, as
/// [`Bundled`] reads them, each beside the module giving its members.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Packed
{
    /// The bundle's theories, the outermost first.
    theories: Vec<BundledTheory>,
    /// The module giving each theory's members, place for place: the packed
    /// module first, then the member module each nested component names.
    modules: Vec<StructureIndex>,
}

/// A theory whose components [`Lowerer::bundled`] is reading.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct BundleFrame
{
    /// The theory's place among the bundle's theories.
    place: usize,
    /// The theory's declaration.
    slot: SlotIndex,
    /// Where the theory's declaration starts, where its nested theories are
    /// read.
    start: ByteOffset,
    /// The next component to read.
    next: usize,
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
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(
        captures: before = seeds.len(),
        ensures: seeds.len() >= before,
    )]
    pub(super) fn seed_families(
        &mut self,
        seeds: &mut Vec<(NodeIndex, Reading)>,
    )
    {
        for family in self.collected.families.iter().skip(self.current.families) {
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
        for check in self
            .collected
            .family_checks
            .range(SlotIndex::from(self.current.slots) ..)
            .map(|(_, check)| check)
        {
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
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_family_applied_to_too_few_indices_is_refused`
    #[spec(ensures: |ret| ret.is_err() || self.plans.get(site.at.node) == Some(&Plan::Expansion(family, applied)))]
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
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
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
                Maybe::Present(value) => values.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
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
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
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
            Maybe::Present(defined) => defined,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
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
    ///   theory marked [`Insertion::Model`], since the source writes the
    ///   theory's name there and not the type; a slot whose component names a
    ///   refused one holds that refusal as a fault, and one naming a component
    ///   that did not lower holds [`LoweringRefusal::UnstatedComponent`] with
    ///   [`ModelFault::Inherited`].
    /// - provides: the declared types [`Self::outcome`] reads for model halves.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CatShape` operations and laws mint the written
    ///   signature's types, and a law over a refused family inherits it.
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_family_of_the_wrong_telescope_is_refused`
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
        for (position, slot) in self
            .collected
            .slots
            .iter()
            .enumerate()
            .skip(self.current.slots)
        {
            let (
                Maybe::Present(Half {
                    declaration,
                    operand: Operand::Model(part),
                    ..
                }),
                Maybe::Absent(_),
                Container::Module(structure),
            ) = (slot.signature, slot.refusal, slot.container)
            else {
                continue;
            };
            let Maybe::Present(written) = self.origin_at(declaration.node)
            else {
                continue;
            };
            let origin = written.inserted(Insertion::Model);
            let position = SlotIndex::from(position);
            match self.mint_component(structure, part, sink, origin) {
                Ok(minted) => {
                    let _first = modelled.insert(position, minted);
                },
                Err(Missing::Refused(refusal)) => {
                    let _first = faults.insert(position, refusal);
                },
                Err(Missing::Unlowered) => {
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
    ///   documentation states it, and a constant's type itself, every node
    ///   carrying `origin`.
    /// - fails: a component the derivation cannot state, a sort or a nested
    ///   model, and one naming a component that did not lower, as unlowered;
    ///   one naming a refused component, with its refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_models`].
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_constant_is_a_value_of_its_type_1226`
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
        let minting = Minting {
            members: Members::Module {
                structure,
                operations: self.operation_names(model),
            },
            origin,
        };

        self.mint_form(form, &minting, sink)
    }

    /// The type an operation, a constant or a law states, its sorts and
    /// operations read where `minting` reads them.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: an operation's or a law's telescope Π, as the module's
    ///   documentation states it, and a constant's type itself, every node
    ///   carrying the minting's origin.
    /// - fails: a sort or a nested model, and a form naming a component that
    ///   did not lower, as unlowered; one naming a refused component, with its
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_component`] and
    ///   [`Self::mint_bundle`].
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value_type(id).is_some()))]
    fn mint_form(
        &self,
        form: &ModelForm,
        minting: &Minting<'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueTypeId, Missing<'source>>
    {
        let origin = minting.origin;
        let (telescope, tail) = match *form {
            ModelForm::Operation {
                ref telescope,
                ref results,
            } => (telescope, Tail::Results(results)),
            ModelForm::Law {
                ref telescope,
                ref carrier,
                ref left,
                ref right,
            } => (telescope, Tail::Path(carrier, left, right)),
            ModelForm::Constant(ref sort) => {
                let closed = Context {
                    binders: &[],
                    dependent: &[],
                };
                return self.sort_type(sort, closed, minting, sink);
            },
            ModelForm::Sort { .. } | ModelForm::Nested(_) => return Err(Missing::Unlowered),
        };
        let dependent = dependence(telescope, tail);
        let mut domains = Vec::with_capacity(telescope.len());
        for (depth, binder) in telescope.iter().enumerate() {
            let context = Context {
                binders: telescope.get(.. depth).unwrap_or_default(),
                dependent: dependent.get(.. depth).unwrap_or_default(),
            };
            domains.push(self.sort_type(&binder.sort, context, minting, sink)?);
        }
        let context = Context {
            binders: telescope,
            dependent: &dependent,
        };
        let codomain = match tail {
            Tail::Results(results) => {
                let mut sorts = Vec::with_capacity(results.len());
                for result in results {
                    sorts.push(self.sort_type(result, context, minting, sink)?);
                }
                if let [one] = *sorts.as_slice() {
                    one
                }
                else {
                    let id = sink.arena.value_type_product(&sorts);
                    sink.origins.record_value_type(id, origin);
                    id
                }
            },
            Tail::Path(carrier, left, right) => {
                let over = self.sort_type(carrier, context, minting, sink)?;
                let from = self.term_value(left, context, minting, sink)?;
                let to = self.term_value(right, context, minting, sink)?;
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

    /// Each operation and constant of `model`, by its name in the theory, with
    /// the member name the module reads it under and how a term reads it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per operation and constant component, its name
    ///   tile's text the member name, a constant held and an operation applied.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp` and `id` are found for the `CatShape` laws.
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_constant_is_a_value_of_its_type_1226`
    #[spec(ensures: |ret| ret.len() <= model.components.len())]
    fn operation_names(
        &self,
        model: &ModelSignature,
    ) -> BTreeMap<Name, (SurfaceName<'source>, MemberRead)>
    {
        model
            .components
            .iter()
            .filter_map(|component| {
                let read = match component.form {
                    Ok(ModelForm::Operation { .. }) => MemberRead::Applied,
                    Ok(ModelForm::Constant(_)) => MemberRead::Held,
                    Ok(ModelForm::Sort { .. } | ModelForm::Law { .. } | ModelForm::Nested(_))
                    | Err(_) => return None,
                };
                Some((
                    component.name.clone(),
                    (self.name_at(component.named), read),
                ))
            })
            .collect()
    }

    /// The type the sort term `sort` names, read under `context`.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: for a sort the bundle fixes, the type it is, raised past the
    ///   binders between the record's outside and the reading; for a sort a
    ///   bundle field before the minted one states, the decode at the fuss-free
    ///   level of that field's variable, or for an indexed sort of the call
    ///   [`Self::family_call`] mints; for an unindexed sort, the type its
    ///   component reads — the member's type, or the atom a sealed component
    ///   declares — or, where no type component bears its name, the builtin
    ///   type it names; for an indexed one, its family expanded over the index
    ///   terms' values.
    /// - fails: a sort no type component of the module or field answers and no
    ///   builtin type names, of another index count, or whose type did not
    ///   lower, as unlowered; one whose component is refused, with its refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Ob` reads the universe the member writes and `Hom(a,
    ///   b)` the member's family over two variables.
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::an_operation_at_a_builtin_type_derives_it_1226`
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    /// - witness: `tests::modules::models::a_family_sort_is_a_function_into_the_universe`
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value_type(id).is_some()))]
    fn sort_type(
        &self,
        sort: &SortTerm,
        context: Context<'_>,
        minting: &Minting<'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueTypeId, Missing<'source>>
    {
        let structure = match minting.members {
            Members::Module { structure, .. } => Some(structure),
            Members::Fields(fields) => {
                if let (Some((stated, lift)), true) = (
                    fields.manifest(&sort.sort, context),
                    sort.indices.is_empty(),
                ) {
                    let lifted = gandr_core_term::shift_value_type(sink.arena, stated, lift);
                    return Ok(lifted.settle(sink.arena));
                }
                if let Some(at) = fields.index(&sort.sort, context) {
                    let code = if sort.indices.is_empty() {
                        let head = sink.arena.value_variable(Zone::Intuitionistic, at);
                        sink.origins.record_value(head, minting.origin);
                        head
                    }
                    else {
                        self.family_call(at, &sort.indices, context, minting, sink)?
                    };
                    let id = sink
                        .arena
                        .value_type_element(code, Level::constant(Universe::FUSS_FREE.level));
                    sink.origins.record_value_type(id, minting.origin);
                    return Ok(id);
                }
                None
            },
        };
        let Some(component) = structure
            .and_then(|structure| self.collected.structures.get(usize::from(structure)))
            .and_then(|structure| {
                structure
                    .types
                    .iter()
                    .find(|component| component.name.as_ref() == sort.sort.as_ref())
            })
            .copied()
        else {
            let builtin = match type_atom(SurfaceName::from(sort.sort.as_ref())) {
                Maybe::Present(atom) if sort.indices.is_empty() => sink.atom(atom, minting.origin),
                Maybe::Present(_) | Maybe::Absent(_) => return Err(Missing::Unlowered),
            };
            return match builtin {
                Lowered::ValueType(id) => Ok(id),
                Lowered::Value(_)
                | Lowered::Computation(_)
                | Lowered::CompType(_)
                | Lowered::Function { .. } => Err(Missing::Unlowered),
            };
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
            (TypeMeaning::Manifest(defined), true) => match self.value_type_at(defined.node) {
                Maybe::Present(id) => Ok(id),
                Maybe::Absent(_) => Err(Missing::Unlowered),
            },
            (TypeMeaning::Sealed, true) => {
                let Some(atom) = self.collected.slots.get(usize::from(component.held))
                else {
                    return Err(Missing::Unlowered);
                };
                let id = sink.arena.value_type_abstract(atom.constant);
                sink.origins.record_value_type(id, minting.origin);
                Ok(id)
            },
            (TypeMeaning::Instantiated { defined, instance }, true) => self
                .instance_types
                .get(&(instance, defined.node))
                .copied()
                .ok_or(Missing::Unlowered),
            (TypeMeaning::Family(family), false) => {
                let mut arguments = Vec::with_capacity(sort.indices.len());
                for index in &sort.indices {
                    arguments.push(self.term_value(index, context, minting, sink)?);
                }
                match self.expand(family, &arguments, sink, minting.origin) {
                    Maybe::Present(id) => Ok(id),
                    Maybe::Absent(_) => Err(Missing::Unlowered),
                }
            },
            (
                TypeMeaning::Manifest(_) | TypeMeaning::Sealed | TypeMeaning::Instantiated { .. },
                false,
            )
            | (TypeMeaning::Family(_), true) => Err(Missing::Unlowered),
        }
    }

    /// The returned call of the family field at `at` on the index terms
    /// `indices`, read under `context`, as a written call of a family in a type
    /// lowers.
    ///
    /// # Specification
    /// - requires: `at` is the field's index under `context`.
    /// - ensures: `↑((force x) t₁ … tₙ)` over the index terms' values; an index
    ///   term that applies an operation runs first, `c ← t; …`, one bind per
    ///   such term in written order, the first outermost, the term read as its
    ///   bind's variable and every other value raised past the binds; every
    ///   node carrying the minting's origin.
    /// - fails: an index term that does not mint, as [`Self::term_value`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Termination
    /// Every loop runs once per index term of the finite `indices`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a graph's edges over two variables, and the terms of
    ///   a context extended by a call.
    /// - witness: `tests::modules::models::a_family_sort_is_a_function_into_the_universe`
    /// - witness: `tests::modules::models::a_family_over_an_applied_index_runs_the_call_first`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&code| matches!(sink.arena.value(code), Some(&Value::Returned(_)))))]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `runs` holds the runs among one sort term's indices"
        )
    )]
    fn family_call(
        &self,
        at: DeBruijnIndex,
        indices: &[FreeTerm],
        context: Context<'_>,
        minting: &Minting<'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueId, Missing<'source>>
    {
        let origin = minting.origin;
        let mut passed = Vec::with_capacity(indices.len());
        let mut runs = Vec::new();
        for index in indices {
            let value = self.term_value(index, context, minting, sink)?;
            if let Some(&Value::Returned(run)) = sink.arena.value(value) {
                runs.push((passed.len(), run));
            }
            passed.push(value);
        }
        let past = Binders::from(u32::try_from(runs.len()).unwrap_or(u32::MAX));
        let mark = sink.arena.watermark();
        let mut carried = Vec::new();
        let mut raised = Vec::with_capacity(passed.len());
        for (position, &value) in passed.iter().enumerate() {
            if runs.is_empty() || runs.iter().any(|&(run_at, _)| run_at == position) {
                raised.push(value);
                continue;
            }
            let wrapped = sink.arena.computation_return(value);
            let shifted =
                gandr_core_term::shift_computation_under(sink.arena, wrapped, Binders::NONE, past)
                    .settle_traced(sink.arena, &mut carried);
            raised.push(match sink.arena.computation(shifted) {
                Some(&Computation::Return(inner)) => inner,
                _ => value,
            });
        }
        let mut firsts = Vec::with_capacity(runs.len());
        for (order, &(_, run)) in runs.iter().enumerate() {
            let before = Binders::from(u32::try_from(order).unwrap_or(u32::MAX));
            firsts.push(
                gandr_core_term::shift_computation_under(sink.arena, run, Binders::NONE, before)
                    .settle_traced(sink.arena, &mut carried),
            );
        }
        exits::record_copies(sink, mark, &carried, origin);
        let head = sink.arena.value_variable(
            Zone::Intuitionistic,
            DeBruijnIndex::from(u32::from(at).saturating_add(u32::from(past))),
        );
        sink.origins.record_value(head, origin);
        let mut called = sink.arena.computation_force(head);
        sink.origins.record_computation(called, origin);
        for (position, &value) in raised.iter().enumerate() {
            let argument = match runs.iter().position(|&(run_at, _)| run_at == position) {
                Some(order) => {
                    let index = runs.len().saturating_sub(order).saturating_sub(1);
                    let bound = sink.arena.value_variable(
                        Zone::Intuitionistic,
                        DeBruijnIndex::from(u32::try_from(index).unwrap_or(u32::MAX)),
                    );
                    sink.origins.record_value(bound, origin);
                    bound
                },
                None => value,
            };
            called = sink.arena.computation_application(called, argument);
            sink.origins.record_computation(called, origin);
        }
        for &first in firsts.iter().rev() {
            called = sink.arena.computation_bind(first, called);
            sink.origins.record_computation(called, origin);
        }
        let returned = sink.arena.value_returned(called);
        sink.origins.record_value(returned, origin);

        Ok(returned)
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
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value(id).is_some()))]
    fn term_value(
        &self,
        term: &FreeTerm,
        context: Context<'_>,
        minting: &Minting<'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueId, Missing<'source>>
    {
        let origin = minting.origin;
        let mut pending = Vec::from([Walk::Read(term.to_node())]);
        let mut built: Vec<ValueId> = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                Walk::Read(node) => match node.view() {
                    TermView::Var(name) => {
                        let index = variable(context, name)?;
                        let id = sink.arena.value_variable(Zone::Intuitionistic, index);
                        sink.origins.record_value(id, origin);
                        built.push(id);
                    },
                    TermView::Op { name, args } => {
                        let arguments: Vec<TermNode<'_>> = args.collect();
                        pending.push(Walk::Apply(name, OperandCount::from(arguments.len())));
                        pending.extend(arguments.into_iter().rev().map(Walk::Read));
                    },
                    TermView::Ctor { .. }
                    | TermView::Results { .. }
                    | TermView::Inst { .. }
                    | TermView::Abs { .. } => {
                        return Err(Missing::Unlowered);
                    },
                },
                Walk::Apply(name, count) => {
                    let start = built
                        .len()
                        .checked_sub(usize::from(count))
                        .ok_or(Missing::Unlowered)?;
                    let (head, read) = self.member_head(minting, name, context, sink)?;
                    match read {
                        MemberRead::Held if usize::from(count) == 0 => built.push(head),
                        MemberRead::Held => return Err(Missing::Unlowered),
                        MemberRead::Applied => {
                            let mut applied = sink.arena.computation_force(head);
                            sink.origins.record_computation(applied, origin);
                            for argument in built.drain(start ..) {
                                applied = sink.arena.computation_application(applied, argument);
                                sink.origins.record_computation(applied, origin);
                            }
                            let returned = sink.arena.value_returned(applied);
                            sink.origins.record_value(returned, origin);
                            built.push(returned);
                        },
                    }
                },
            }
        }
        match *built.as_slice() {
            [value] => Ok(value),
            _ => Err(Missing::Unlowered),
        }
    }

    /// The value the operation or constant `name` is read as where `minting`
    /// reads it, under `context`, and how a term reads it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: in a module, the constant of the member it names, as
    ///   [`Self::operation_constant`] finds it; in a bundle, the variable of
    ///   the field before the minted one that states it; the node carries the
    ///   minting's origin.
    /// - fails: a name neither answers, as unlowered; a refused member, with
    ///   its refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp` reads the member `comp`, and a law of a model
    ///   type reads its operation's field.
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(head, _)| sink.arena.value(head).is_some()))]
    fn member_head(
        &self,
        minting: &Minting<'source, '_>,
        name: &Name,
        context: Context<'_>,
        sink: &mut Sink<'_>,
    ) -> Result<(ValueId, MemberRead), Missing<'source>>
    {
        let (head, read) = match minting.members {
            Members::Module {
                structure,
                ref operations,
            } => {
                let (constant, read) = self.operation_constant(structure, operations, name)?;
                (sink.arena.value_constant(constant), read)
            },
            Members::Fields(fields) => {
                let read = match fields
                    .before
                    .iter()
                    .rfind(|component| component.name == *name)
                    .map(|component| &component.form)
                {
                    Some(&Ok(ModelForm::Operation { .. })) => MemberRead::Applied,
                    Some(&Ok(ModelForm::Constant(_))) => MemberRead::Held,
                    Some(
                        &(Ok(
                            ModelForm::Sort { .. } | ModelForm::Law { .. } | ModelForm::Nested(_),
                        )
                        | Err(_)),
                    )
                    | None => return Err(Missing::Unlowered),
                };
                let index = fields.index(name, context).ok_or(Missing::Unlowered)?;
                (sink.arena.value_variable(Zone::Intuitionistic, index), read)
            },
        };
        sink.origins.record_value(head, minting.origin);

        Ok((head, read))
    }

    /// The constant of the member the operation `name` reads in the module at
    /// `structure`, and how a term reads it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the admission position of the member the module declares
    ///   under the operation's name, beside the model's reading of it.
    /// - fails: an operation the model does not declare, or one the module does
    ///   not define, as unlowered; a refused member, with its refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `comp` reads the member `comp`.
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| ret.is_err() || operations.contains_key(name))]
    fn operation_constant(
        &self,
        structure: StructureIndex,
        operations: &BTreeMap<Name, (SurfaceName<'source>, MemberRead)>,
        name: &Name,
    ) -> Result<(ConstantIndex, MemberRead), Missing<'source>>
    {
        let Some(&(member, read)) = operations.get(name)
        else {
            return Err(Missing::Unlowered);
        };
        let Some(&slot) = self
            .collected
            .by_name
            .get(&(Container::Module(structure), member))
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

        Ok((declared.constant, read))
    }

    /// Classify a model type with manifest sorts, `Model(T) with sort x = A`:
    /// the application on its left stands for the form, and reads the sorts
    /// the bindings on its right fix when it classifies.
    ///
    /// # Specification
    /// - requires: `site` is a manifest type, `L with R`.
    /// - ensures: the left operand is read at the form's own reading and
    ///   adopted, and the sorts the bindings fix, down the chain of `with` the
    ///   right operand nests, are filed against it, each sort's name beside the
    ///   type it is, in written order, for [`Self::model_type`] to fix when the
    ///   operand is `Model(T)`.
    /// - fails: a misplaced tile at the `with` when the left operand is no type
    ///   application, and the refusals [`Self::bindings`] yields.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Model(T)` with one manifest sort, with a sort past
    ///   the binders before it and with two, a chain after a head other than
    ///   `Model`, after no application, and over an operand that is no binding.
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    /// - witness: `tests::modules::models::a_manifest_sort_reads_past_the_links_before_it`
    /// - witness: `tests::modules::models::a_manifest_sort_the_theory_cannot_fix_is_refused`
    /// - witness: `tests::modules::models::a_manifest_sort_after_another_head_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(site.at.node),
                    Some(&Plan::Transparent(child))
                        if self.reading(child) == site.reading && self.fixed_sorts.contains_key(&child)
                )
        },
    )]
    pub(super) fn manifest_model(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let applied = site.one(cursor.operands())?;
        let Maybe::Present(with) = cursor.tile(TileName::WITH)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let bound = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        let Some(node) = self.tree.node(applied.node)
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let Shape::Form {
            former: Former::TypeApplication,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Err(site.fault(with.span, FormFault::MisplacedTile));
        };
        let mut sorts = Vec::new();
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = self.bindings(site, bound, &mut scratch, &mut sorts);
        self.scratch = scratch;
        read?;
        let _earlier = self.fixed_sorts.insert(applied.node, sorts);
        self.read(applied.node, site.reading);

        self.plan(site, Plan::Transparent(applied.node));

        Ok(())
    }

    /// Read into `sorts` the sorts the bindings `bound` writes fix, down the
    /// chain of `with` their right operands nest: `sort x = A with sort y =
    /// B` is one binding on the left of a `with` whose right is the rest.
    ///
    /// # Specification
    /// - requires: `bound` is the right operand of the manifest type `site`;
    ///   `scratch` is free to overwrite.
    /// - ensures: one entry per binding, the sort's name beside the type it is,
    ///   in written order.
    /// - fails: the refusals [`Self::binding`] yields, and the form's refusal
    ///   for a `with` out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Termination
    /// Every pass descends to the right operand of a `with`, a node strictly
    /// inside the one before it in the finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one binding and two, each sort beside its type in
    ///   order, and an operand that is no binding.
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    /// - witness: `tests::modules::models::a_manifest_sort_the_theory_cannot_fix_is_refused`
    #[spec(captures: before = sorts.len(), ensures: |ret| ret.is_err() || sorts.len() > before)]
    fn bindings(
        &self,
        site: Site,
        bound: Placed,
        scratch: &mut Pieces,
        sorts: &mut Vec<(Placed, Placed)>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut link = bound;
        loop {
            let Some(node) = self.tree.node(link.node)
            else {
                return Err(site.out(FragmentBoundary::Unadmitted));
            };
            let Shape::Form {
                former: Former::ManifestType,
                ..
            } = shape_of(self.pbg, node)?
            else {
                sorts.push(self.binding(site, link, scratch)?);
                return Ok(());
            };
            read_pieces(self.pbg, self.tree, link.node, scratch)?;
            let mut cursor = Cursor::new(&scratch.pieces, link.span);
            let first = site.one(cursor.operands())?;
            closed(site, &mut cursor, TileName::WITH)?;
            let rest = site.one(cursor.operands())?;
            exhausted(site, &cursor)?;
            sorts.push(self.binding(site, first, scratch)?);
            link = rest;
        }
    }

    /// The sort the binding `at` fixes, `sort x = A`: its name beside the
    /// type it is.
    ///
    /// # Specification
    /// - requires: `at` stands on the right of a `with` of the manifest type
    ///   `site`; `scratch` is free to overwrite.
    /// - ensures: the binding's sort name and its one type operand.
    /// - fails: an extra operand at an operand that is no binding, a misplaced
    ///   tile where the sort's name or `=` is missing, and the hole's own
    ///   refusal for a binding with no type.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binding read beside its type, and an operand that
    ///   is no binding.
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    /// - witness: `tests::modules::models::a_manifest_sort_the_theory_cannot_fix_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(sort, defined)| at.span.start() <= sort.span.start() && defined.span.end() <= at.span.end()))]
    fn binding(
        &self,
        site: Site,
        at: Placed,
        scratch: &mut Pieces,
    ) -> Result<(Placed, Placed), LoweringRefusal<'source>>
    {
        read_pieces(self.pbg, self.tree, at.node, scratch)?;
        let mut cursor = Cursor::new(&scratch.pieces, at.span);
        if let Maybe::Absent(_) = cursor.tile(TileName::SORT) {
            return Err(site.fault(at.span, FormFault::ExtraOperand));
        }
        let Maybe::Present(sort) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::EQUALS) {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        }
        let defined = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;

        Ok((sort, defined))
    }

    /// Classify a theory's models as a type, `Model(S)`, its operand read off
    /// the application, closed by the manifest sorts `manifests`.
    ///
    /// # Specification
    /// - requires: `site` is a type application headed `Model`, which nothing
    ///   the scope binds answers, written over `theory`; `manifests` is each
    ///   manifest sort's name beside the type it is, in written order.
    /// - ensures: the form stands as a value type and is planned over the
    ///   bundle [`Self::bundled`] reads off the theory the operand names, the
    ///   outermost theory without the sorts `manifests` fixes; each fixed
    ///   sort's type is read as a value type, and the operand as the theory's
    ///   name alone.
    /// - fails: yields the wrong-sort refusal where no value type is read; an
    ///   operand that is no capitalised name is out of the fragment; the
    ///   refusals [`Self::bundled`] yields; a sort fixed twice is a duplicate
    ///   definition, an indexed one an unread ascription, and a name that is no
    ///   sort of the theory an unknown member.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Termination
    /// The loop runs once per manifest sort of the finite form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Model(Toggle)` beside the record it abbreviates, a
    ///   law-bearing theory's beside its own, a name no theory answers, a
    ///   toggle whose carrier is fixed, and a sort fixed twice, an indexed one
    ///   and a member that is no sort.
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    /// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
    /// - witness: `tests::modules::models::a_model_type_of_an_undeclared_theory_is_refused`
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    /// - witness: `tests::modules::models::a_manifest_sort_the_theory_cannot_fix_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Bundle(_))))]
    pub(super) fn model_type(
        &mut self,
        site: Site,
        theory: NodeIndex,
        manifests: &[(Placed, Placed)],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let Some(node) = self.tree.node(theory)
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let named = Placed::of(theory, node);
        let written = Site { at: named, ..site };
        let Shape::Form {
            former: Former::TypeHead | Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Err(written.out(FragmentBoundary::Unadmitted));
        };
        let module = self.name_at(named);
        let mut theories = self.bundled(written, (site.at.span.start(), module))?;
        let Some(outermost) = theories.first_mut()
        else {
            return Err(written.out(FragmentBoundary::Unadmitted));
        };
        let mut fixed = Vec::with_capacity(manifests.len());
        for (place, &(sort, defined)) in manifests.iter().enumerate() {
            let member = self.name_at(sort);
            if let Some(&(first, _)) = manifests
                .get(.. place)
                .unwrap_or_default()
                .iter()
                .find(|&&(earlier, _)| self.name_at(earlier) == member)
            {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: sort.span,
                    name: member,
                    first: first.span,
                });
            }
            let components = &mut outermost.signature.components;
            let at = components
                .iter()
                .position(|component| component.name.as_ref() == member.as_ref());
            match at
                .and_then(|at| components.get(at))
                .map(|component| &component.form)
            {
                Some(&Ok(ModelForm::Sort { ref indices })) if indices.is_empty() => {},
                Some(&Ok(ModelForm::Sort { .. })) => {
                    return Err(LoweringRefusal::UnreadAscription {
                        span: sort.span,
                        name: member,
                        form: AscriptionForm::Parameterized,
                    });
                },
                Some(
                    &(Ok(
                        ModelForm::Operation { .. }
                        | ModelForm::Constant(_)
                        | ModelForm::Nested(_)
                        | ModelForm::Law { .. },
                    )
                    | Err(_)),
                )
                | None => {
                    return Err(LoweringRefusal::UnknownMember {
                        span: sort.span,
                        module,
                        member,
                    });
                },
            }
            if let Some(at) = at {
                let component = components.remove(at);
                fixed.push((component.name, defined.node));
            }
            self.read(defined.node, Reading::ValueType(frame));
        }
        let bundled = Bundled {
            theories,
            named: theory,
            manifests: fixed,
        };
        self.plan(site, Plan::Bundle(Arc::new(bundled)));

        Ok(())
    }

    /// The fields a pattern splits at the type `stated`, when it is a
    /// theory's models and their record nests pairs.
    ///
    /// # Specification
    /// - requires: `stated` is a type's syntax node, already classified.
    /// - ensures: through the transparent plans of parentheses, for a type
    ///   planned as `Model(T)` whose outermost record has a field a later one
    ///   names, one entry per component of `T`'s signature in signature order,
    ///   labelled by the component's name and placed at `at`, beside whether
    ///   each but the last binds the ones after it, as [`Self::bundle_type`]
    ///   nests them; the other-former absence for a bundle keyed by names,
    ///   which a pattern splits as the record it is, and for every other type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each step follows a transparent plan to the child it stands for,
    /// strictly deeper in the finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positional and a labelled pattern at a toggle's
    ///   models bind its carrier, its start, its step and its reading.
    /// - witness: `tests::modules::models::a_pattern_at_a_model_type_splits_its_fields`
    #[spec(ensures: |ret| match ret {
        Maybe::Present((ref entries, ref links)) => links.len().saturating_add(1) == entries.len(),
        Maybe::Absent(_) => true,
    })]
    pub(super) fn stated_bundle(
        &self,
        stated: NodeIndex,
        at: Placed,
    ) -> Maybe<(Vec<arity::Entry<'source>>, Vec<arity::Dependent>), related::Absent>
    {
        let otherwise = Maybe::Absent(related::Absent::Otherwise);
        let mut node = stated;
        let bundled = loop {
            match self.plans.get(node) {
                Some(&Plan::Transparent(inner)) => node = inner,
                Some(&Plan::Bundle(ref bundled)) => break bundled,
                _ => return otherwise,
            }
        };
        let Some(theory) = bundled.theories.first()
        else {
            return otherwise;
        };
        let binds = bundle_dependence(&theory.signature);
        if !binds.iter().any(|binds| binds.0) {
            return otherwise;
        }
        let entries: Vec<arity::Entry<'source>> = theory
            .signature
            .components
            .iter()
            .map(|component| arity::Entry {
                key: arity::Key::Label(self.name_at(component.named), at),
                held: arity::Held::Operand(at),
            })
            .collect();
        let links = binds
            .iter()
            .take(entries.len().saturating_sub(1))
            .map(|binds| arity::Dependent(binds.0))
            .collect();

        Maybe::Present((entries, links))
    }

    /// The theories of the bundle the theory `name` names where a form
    /// starting at `at` stands, its refusals placed at `written`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the signature the theory derives first, then, depth first in
    ///   the order the components stand, the signature of each theory a nested
    ///   component names, read where the nesting theory's declaration starts,
    ///   each theory beside the places of the theories it nests.
    /// - fails: the refusals [`crate::module::Collected::presented_theory`]
    ///   yields; an unadmitted form for a theory whose value codes no
    ///   presentation or that nests itself; a component the signature cannot
    ///   state, refused by name with its fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnstatedComponent`],
    /// [`LoweringRefusal::OutOfFragment`] and the refusals of
    /// [`crate::module::Collected::presented_theory`].
    ///
    /// # Termination
    /// Every pass advances the top frame past one component or pops it. A
    /// frame is pushed only for a theory no frame on the stack holds, so the
    /// stack is no deeper than the unit's finite slots, and each frame reads
    /// its signature's finite components once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a theory of sorts and operations, one with a law, one
    ///   with a family sort, one nesting another, and a name no theory answers.
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    /// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
    /// - witness: `tests::modules::models::a_family_sort_is_a_function_into_the_universe`
    /// - witness: `tests::modules::models::a_nesting_model_type_bundles_the_inner_one`
    /// - witness: `tests::modules::models::a_model_type_of_an_undeclared_theory_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |theories| !theories.is_empty()))]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: one search of the unit's slots and of the frame stack per nested component, and a bundle nests few"
        )
    )]
    fn bundled(
        &mut self,
        written: Site,
        (at, name): (ByteOffset, SurfaceName<'source>),
    ) -> Result<Vec<BundledTheory>, LoweringRefusal<'source>>
    {
        let span = written.at.span;
        // The outermost theory is the one the written type names: it reaches
        // the import of the source declaring it.
        let crossed = match self.collected.presented_theory(at, span, name) {
            Ok((position, _)) => self.collected.slots.get(usize::from(position)).map(|slot| {
                (
                    self.collected.unit.source_at(at),
                    self.collected.unit.source_at(slot.named.span.start()),
                )
            }),
            Err(_) => None,
        };
        if let Some((using, declaring)) = crossed
            && using != declaring
        {
            self.collected.reach_source(using, declaring);
        }
        let read = |at: ByteOffset, name: SurfaceName<'source>| {
            let (position, presentation) = self.collected.presented_theory(at, span, name)?;
            let Ok(signature) = crate::model::derive(presentation)
            else {
                return Err(written.out(FragmentBoundary::Unadmitted));
            };
            let start = self
                .collected
                .slots
                .get(usize::from(position))
                .map_or(at, |slot| slot.introduced_by.span.start());
            Ok((position, start, signature))
        };
        let (slot, start, signature) = read(at, name)?;
        let mut theories = vec![BundledTheory {
            signature,
            nested: Vec::new(),
        }];
        let mut frames = vec![BundleFrame {
            place: 0,
            slot,
            start,
            next: 0,
        }];
        while let Some(frame) = frames.last_mut() {
            let Some(component) = theories
                .get(frame.place)
                .and_then(|theory| theory.signature.components.get(frame.next))
            else {
                let _done = frames.pop();
                continue;
            };
            frame.next = frame.next.saturating_add(1);
            let (parent, start) = (frame.place, frame.start);
            let theory = match component.form {
                Ok(ModelForm::Nested(ref theory)) => theory.clone(),
                Ok(
                    ModelForm::Sort { .. }
                    | ModelForm::Operation { .. }
                    | ModelForm::Constant(_)
                    | ModelForm::Law { .. },
                ) => continue,
                Err(fault) => {
                    return Err(LoweringRefusal::UnstatedComponent {
                        span,
                        name: self.name_at(component.named),
                        fault,
                    });
                },
            };
            let Some(name) = self
                .collected
                .slots
                .iter()
                .find(|slot| slot.name.as_ref() == theory.as_ref())
                .map(|slot| slot.name)
            else {
                return Err(written.out(FragmentBoundary::Unadmitted));
            };
            let (slot, start, signature) = read(start, name)?;
            if frames.iter().any(|frame| frame.slot == slot) {
                return Err(written.out(FragmentBoundary::Unadmitted));
            }
            let place = theories.len();
            if let Some(parent) = theories.get_mut(parent) {
                parent.nested.push(place);
            }
            theories.push(BundledTheory {
                signature,
                nested: Vec::new(),
            });
            frames.push(BundleFrame {
                place,
                slot,
                start,
                next: 0,
            });
        }

        Ok(theories)
    }

    /// Mint a theory's models as a type: the bundled record `bundled` states.
    ///
    /// # Specification
    /// - requires: every theory of `bundled` nests only theories after it, as
    ///   [`Self::bundled`] reads them.
    /// - ensures: the outermost theory's record as [`Self::bundle_type`] mints
    ///   it, reading each manifest sort as the type it is, each nested
    ///   component's field the record of its theory, minted before the theory
    ///   nesting it; the record carrying `origin` and every node below it the
    ///   theory's name marked [`Insertion::Model`], since the source writes the
    ///   name and not the record; nothing when a field or a manifest sort's
    ///   type does not mint.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per theory of the finite bundle.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::bundle_type`], and a theory nesting
    ///   another bundles the inner record as a field.
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    /// - witness: `tests::modules::models::a_nesting_model_type_bundles_the_inner_one`
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_bundle(
        &self,
        bundled: &Bundled,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let below = match self.origin_at(bundled.named) {
            Maybe::Present(named) => named.inserted(Insertion::Model),
            Maybe::Absent(_) => origin.inserted(Insertion::Model),
        };
        let fixed: Option<Vec<(&Name, ValueTypeId)>> = bundled
            .manifests
            .iter()
            .map(|&(ref name, defined)| match self.value_type_at(defined) {
                Maybe::Present(id) => Some((name, id)),
                Maybe::Absent(_) => None,
            })
            .collect();
        let Some(fixed) = fixed
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let mut minted: Vec<Option<ValueTypeId>> = vec![None; bundled.theories.len()];
        for (place, theory) in bundled.theories.iter().enumerate().rev() {
            let nested: Option<Vec<ValueTypeId>> = theory
                .nested
                .iter()
                .map(|&inner| minted.get(inner).copied().flatten())
                .collect();
            let Some(nested) = nested
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let top = if place == 0 { origin } else { below };
            let manifests = if place == 0 { fixed.as_slice() } else { &[] };
            let Ok(id) =
                self.bundle_type(&theory.signature, &nested, manifests, sink, (top, below))
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            if let Some(at) = minted.get_mut(place) {
                *at = Some(id);
            }
        }
        minted
            .first()
            .copied()
            .flatten()
            .map_or(Maybe::Absent(lowered::Absent::Unminted), |id| {
                Maybe::Present(Lowered::ValueType(id))
            })
    }

    /// Classify a module packed at its model type, `pack M at Model(S)`.
    ///
    /// # Specification
    /// - requires: `site` is a pack-at form and `cursor` stands before its
    ///   `pack` tile.
    /// - ensures: the form stands as a value and is planned over the theories
    ///   [`Self::bundled`] reads off the theory `S` names, the outermost beside
    ///   the top-level module `M` names, declared before the form, and each
    ///   nested one beside the member module its component names in the module
    ///   nesting it.
    /// - fails: the wrong-sort refusal where no value is read; a misplaced or
    ///   missing piece; a module operand that is no capitalised name, or a
    ///   stated type that is not `Model(S)`, out of the fragment; a name no
    ///   module declared before answers, unresolved; a component no member of
    ///   its module answers, an unknown member; an unindexed sort its module
    ///   seals or states as a family, out of the fragment as a pack; the
    ///   refusals [`Self::bundled`] yields.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Termination
    /// The outer loop visits each theory of the finite bundle once, the inner
    /// one each of its finite components once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's module packed at its models, the same
    ///   module sealed, and a name no module answers.
    /// - witness: `tests::modules::models::a_manifest_module_packs_as_the_record_of_its_members`
    /// - witness: `tests::modules::models::a_pack_of_a_sealed_sort_is_refused`
    /// - witness: `tests::modules::models::a_pack_of_no_module_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Packed(_))))]
    pub(super) fn pack_model(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        super::closed(site, &mut cursor, TileName::PACK)?;
        let module = site.one(cursor.operands())?;
        super::closed(site, &mut cursor, TileName::AT)?;
        let stated = site.one(cursor.operands())?;
        super::exhausted(site, &cursor)?;
        let Ok(Some((_, Former::Constructor | Former::TypeHead))) = self.form_at(module)
        else {
            return Err(Site { at: module, ..site }.out(FragmentBoundary::Unadmitted));
        };
        let theory = self.stated_theory(Site { at: stated, ..site })?;
        let name = self.name_at(module);
        let Some(outermost) = self.collected.structures.iter().rposition(|structure| {
            structure.name.as_ref() == name.as_ref()
                && matches!(structure.container, Container::TopLevel(_))
                && matches!(structure.stratum, Stratum::Module)
                && structure.declared_by.span.end() <= site.at.span.start()
        })
        else {
            return Err(LoweringRefusal::UnresolvedName {
                span: module.span,
                name,
            });
        };
        let written = Site { at: theory, ..site };
        let theories = self.bundled(written, (site.at.span.start(), self.name_at(theory)))?;
        let mut modules = vec![StructureIndex::from(outermost); theories.len()];
        for (place, read) in theories.iter().enumerate() {
            let Some(&holder) = modules.get(place)
            else {
                continue;
            };
            let mut nested = read.nested.iter();
            for component in &read.signature.components {
                let member = self.name_at(component.named);
                let unknown = LoweringRefusal::UnknownMember {
                    span: module.span,
                    module: name,
                    member,
                };
                match component.form {
                    Ok(ModelForm::Nested(_)) => {
                        let Maybe::Present(inner) = self.member_module(holder, member)
                        else {
                            return Err(unknown);
                        };
                        if let Some(&at) = nested.next()
                            && let Some(given) = modules.get_mut(at)
                        {
                            *given = inner;
                        }
                    },
                    Ok(ModelForm::Sort { ref indices }) if indices.is_empty() => {
                        match self.member_type(holder, member) {
                            Maybe::Present(
                                TypeMeaning::Manifest(_) | TypeMeaning::Instantiated { .. },
                            ) => {},
                            Maybe::Present(TypeMeaning::Sealed | TypeMeaning::Family(_)) => {
                                return Err(site.out(FragmentBoundary::Unadmitted));
                            },
                            Maybe::Absent(_) => return Err(unknown),
                        }
                    },
                    Ok(
                        ModelForm::Sort { .. }
                        | ModelForm::Operation { .. }
                        | ModelForm::Constant(_)
                        | ModelForm::Law { .. },
                    ) => {
                        if !self
                            .collected
                            .by_name
                            .contains_key(&(Container::Module(holder), member))
                        {
                            return Err(unknown);
                        }
                    },
                    Err(fault) => {
                        return Err(LoweringRefusal::UnstatedComponent {
                            span: site.at.span,
                            name: member,
                            fault,
                        });
                    },
                }
            }
        }
        self.plan(site, Plan::Packed(Arc::new(Packed { theories, modules })));

        Ok(())
    }

    /// The theory's name `S` the type `Model(S)` written at `site` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the operand's tile, when the type is the application of the
    ///   head `Model` to one capitalised name.
    /// - fails: any other type, out of the fragment; an unknown mold.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pack_model`].
    /// - witness: `tests::modules::models::a_manifest_module_packs_as_the_record_of_its_members`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |theory| theory.span.start() >= site.at.span.start() && theory.span.end() <= site.at.span.end()))]
    fn stated_theory(
        &self,
        site: Site,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        let refused = site.out(FragmentBoundary::Unadmitted);
        let Some((_, Former::TypeApplication)) = self.form_at(site.at)?
        else {
            return Err(refused);
        };
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, site.at.node, &mut pieces)?;
        let mut cursor = Cursor::new(&pieces.pieces, site.at.span);
        let Maybe::Present(head) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(refused);
        };
        if self.name_at(head).as_ref() != super::MODEL {
            return Err(refused);
        }
        let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN)
        else {
            return Err(refused);
        };
        let crate::form::Run::One(theory) = cursor.operands()
        else {
            return Err(refused);
        };
        let Ok(Some((_, Former::Constructor | Former::TypeHead))) = self.form_at(theory)
        else {
            return Err(refused);
        };

        Ok(theory)
    }

    /// The member module of the module at `holder` that `name` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first module member so named; the unresolved absence when
    ///   none is.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the result is the search itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pack_model`].
    /// - witness: `tests::modules::models::a_manifest_module_packs_as_the_record_of_its_members`
    fn member_module(
        &self,
        holder: StructureIndex,
        name: SurfaceName<'source>,
    ) -> Maybe<StructureIndex, super::named::Absent>
    {
        self.collected
            .structures
            .get(usize::from(holder))
            .and_then(|structure| {
                structure.members.iter().find_map(|&member| match member {
                    Member::Module(inner)
                        if self
                            .collected
                            .structures
                            .get(usize::from(inner))
                            .is_some_and(|entry| entry.name.as_ref() == name.as_ref()) =>
                    {
                        Some(inner)
                    },
                    Member::Module(_) | Member::Slot(_) => None,
                })
            })
            .map_or(
                Maybe::Absent(super::named::Absent::Unresolved),
                Maybe::Present,
            )
    }

    /// What the type component of the module at `holder` that `name` names
    /// reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the meaning of the component so named; the unresolved absence
    ///   when none is.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the result is the search itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pack_model`].
    /// - witness: `tests::modules::models::a_pack_of_a_sealed_sort_is_refused`
    fn member_type(
        &self,
        holder: StructureIndex,
        name: SurfaceName<'source>,
    ) -> Maybe<TypeMeaning, super::named::Absent>
    {
        self.collected
            .structures
            .get(usize::from(holder))
            .and_then(|structure| {
                structure
                    .types
                    .iter()
                    .find(|component| component.name.as_ref() == name.as_ref())
            })
            .map_or(
                Maybe::Absent(super::named::Absent::Unresolved),
                |component| Maybe::Present(component.meaning),
            )
    }

    /// Mint a module packed at its model type: the bundled record of the
    /// members `packed` reads.
    ///
    /// # Specification
    /// - requires: every theory of `packed` nests only theories after it, as
    ///   [`Self::bundled`] reads them, each beside the module giving its
    ///   members, as [`Self::pack_model`] plans them.
    /// - ensures: for each theory, the innermost first, one value per component
    ///   in signature order — an unindexed sort the code of the type its module
    ///   states, a nested model the record of its member module, and every
    ///   other component the module's member of its name — nested to the right
    ///   as [`Self::bundle_type`] nests the fields: the pair of a value and the
    ///   rest, and the record keyed by the components' names when no field
    ///   names another; the record carrying `origin` and every node below it
    ///   the same origin marked [`Insertion::Model`], since the source writes
    ///   the module and not the record; nothing when a member did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per theory of the finite bundle, the inner one once
    /// per component of its finite signature.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pack_model`].
    /// - witness: `tests::modules::models::a_manifest_module_packs_as_the_record_of_its_members`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Value(_))))]
    pub(super) fn mint_packed(
        &self,
        packed: &Packed,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let below = origin.inserted(Insertion::Model);
        let mut minted: Vec<Option<ValueId>> = vec![None; packed.theories.len()];
        let mut values = Vec::new();
        for (place, theory) in packed.theories.iter().enumerate().rev() {
            let Some(&module) = packed.modules.get(place)
            else {
                return unminted;
            };
            let mut nested = theory.nested.iter();
            values.clear();
            for component in &theory.signature.components {
                let name = self.name_at(component.named);
                let value = match component.form {
                    Ok(ModelForm::Nested(_)) => nested
                        .next()
                        .and_then(|&inner| minted.get(inner).copied().flatten()),
                    Ok(ModelForm::Sort { ref indices }) if indices.is_empty() => {
                        self.packed_sort(module, name, sink, below)
                    },
                    Ok(
                        ModelForm::Sort { .. }
                        | ModelForm::Operation { .. }
                        | ModelForm::Constant(_)
                        | ModelForm::Law { .. },
                    ) => self
                        .collected
                        .by_name
                        .get(&(Container::Module(module), name))
                        .and_then(|&slot| self.collected.slots.get(usize::from(slot)))
                        .filter(|declared| matches!(declared.refusal, Maybe::Absent(_)))
                        .map(|declared| {
                            let id = sink.arena.value_constant(declared.constant);
                            sink.origins.record_value(id, below);
                            id
                        }),
                    Err(_) => None,
                };
                let Some(value) = value
                else {
                    return unminted;
                };
                values.push(value);
            }
            let top = if place == 0 { origin } else { below };
            let Some(id) = packed_record(&theory.signature, &values, sink, (top, below))
            else {
                return unminted;
            };
            if let Some(at) = minted.get_mut(place) {
                *at = Some(id);
            }
        }
        minted
            .first()
            .copied()
            .flatten()
            .map_or(unminted, |id| Maybe::Present(Lowered::Value(id)))
    }

    /// The code of the type the module at `module` states for its sort
    /// `name`.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: the quote of the type a manifest component's definition
    ///   lowered to, or an instance's renaming of it, carrying `origin`;
    ///   nothing for a component the module seals, states as a family or does
    ///   not hold, or whose type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pack_model`].
    /// - witness: `tests::modules::models::a_manifest_module_packs_as_the_record_of_its_members`
    #[spec(ensures: |ret| ret.is_none_or(|id| matches!(sink.arena.value(id), Some(&Value::Quote(_)))))]
    fn packed_sort(
        &self,
        module: StructureIndex,
        name: SurfaceName<'source>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Option<ValueId>
    {
        let component = self
            .collected
            .structures
            .get(usize::from(module))?
            .types
            .iter()
            .find(|component| component.name.as_ref() == name.as_ref())?;
        let stated = match component.meaning {
            TypeMeaning::Manifest(defined) => match self.value_type_at(defined.node) {
                Maybe::Present(id) => id,
                Maybe::Absent(_) => return None,
            },
            TypeMeaning::Instantiated { defined, instance } => {
                *self.instance_types.get(&(instance, defined.node))?
            },
            TypeMeaning::Sealed | TypeMeaning::Family(_) => return None,
        };
        let id = sink.arena.value_quote(stated);
        sink.origins.record_value(id, origin);

        Some(id)
    }

    /// The bundled record `signature` states, each nested component's field
    /// the matching type of `nested` and each sort `manifests` fixes read as
    /// the type it is.
    ///
    /// # Specification
    /// - requires: every component of the signature states its form, `nested`
    ///   holds one type per nested component, in order, and `manifests` names
    ///   no component of the signature, each type read outside the record.
    /// - ensures: one field per component in signature order — a sort as
    ///   [`Self::sort_field`] states it, a constant its sort, an operation or a
    ///   law its telescope Π as [`Self::mint_form`] states it, a nested model
    ///   its type of `nested` — each sort and operation a field names read as
    ///   the variable of the field stating it, and each sort `manifests` fixes
    ///   as its type raised past the binders before the reading; the fields
    ///   nested to the right as a written dependent record lowers: `Σ` over a
    ///   field a later one names, the eager product of two otherwise, and the
    ///   record keyed by the components' names when no field names another; the
    ///   record carrying `top` and every node below it `below`.
    /// - fails: a field that does not mint, as unlowered.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing::Unlowered`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the toggle's bundle is its written dependent record
    ///   node for node, a law-bearing theory's is its own written record with a
    ///   `Path` field, a family sort is a function into the universe its later
    ///   fields call, and a theory nesting another holds the inner record as a
    ///   field.
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    /// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
    /// - witness: `tests::modules::models::a_family_sort_is_a_function_into_the_universe`
    /// - witness: `tests::modules::models::a_nesting_model_type_bundles_the_inner_one`
    /// - witness: `tests::modules::models::a_manifest_model_type_writes_its_sort_as_its_type`
    /// - witness: `tests::modules::models::a_manifest_sort_reads_past_the_links_before_it`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value_type(id).is_some()))]
    fn bundle_type(
        &self,
        signature: &ModelSignature,
        nested: &[ValueTypeId],
        manifests: &[(&Name, ValueTypeId)],
        sink: &mut Sink<'_>,
        (top, below): (Origin, Origin),
    ) -> Result<ValueTypeId, Missing<'source>>
    {
        let components = &signature.components;
        let binds = bundle_dependence(signature);
        let mut nested = nested.iter();
        let mut fields = Vec::with_capacity(components.len());
        for (at, component) in components.iter().enumerate() {
            let minting = Minting {
                members: Members::Fields(Fields {
                    before: components.get(.. at).unwrap_or_default(),
                    binds: binds.get(.. at).unwrap_or_default(),
                    manifests,
                }),
                origin: below,
            };
            let field = match component.form {
                Ok(ModelForm::Sort { ref indices }) => self.sort_field(indices, &minting, sink)?,
                Ok(ModelForm::Nested(_)) => *nested.next().ok_or(Missing::Unlowered)?,
                Ok(ref form) => self.mint_form(form, &minting, sink)?,
                Err(_) => return Err(Missing::Unlowered),
            };
            fields.push(field);
        }
        if !binds.iter().any(|binds| binds.0) {
            let record = components
                .iter()
                .zip(fields)
                .map(|(component, id)| {
                    (FieldLabel::from(String::from(component.name.as_ref())), id)
                })
                .collect();
            let id = sink.arena.value_type_record(record);
            sink.origins.record_value_type(id, top);
            return Ok(id);
        }
        let Some((&last, earlier)) = fields.split_last()
        else {
            return Err(Missing::Unlowered);
        };
        let mut chained = last;
        for (link, (&first, &binds)) in earlier.iter().zip(&binds).enumerate().rev() {
            chained = if binds.0 {
                sink.arena.value_type_sigma(first, chained)
            }
            else {
                sink.arena.value_type_product(&[first, chained])
            };
            sink.origins
                .record_value_type(chained, if link == 0 { top } else { below });
        }

        Ok(chained)
    }

    /// The field a sort over the index telescope `indices` states.
    ///
    /// # Specification
    /// - requires: `minting` reads the fields before the sort's.
    /// - ensures: the fuss-free universe for an unindexed sort; for an indexed
    ///   one, the function from its indices into that universe, `+U` over one
    ///   binder per index, dependent exactly where a later index's sort names
    ///   it, into the universe's returner — as the written `(a : A, …) => Type`
    ///   lowers; every node carrying the minting's origin.
    /// - fails: an index whose sort does not mint, as [`Self::sort_type`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Missing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the toggle's carrier and a graph's edges over two
    ///   vertices.
    /// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
    /// - witness: `tests::modules::models::a_family_sort_is_a_function_into_the_universe`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value_type(id).is_some()))]
    fn sort_field(
        &self,
        indices: &[Binder],
        minting: &Minting<'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueTypeId, Missing<'source>>
    {
        let origin = minting.origin;
        let universe = sink.arena.value_type_universe(
            Sort::Ground(Universe::FUSS_FREE.sort),
            Level::constant(Universe::FUSS_FREE.level),
        );
        sink.origins.record_value_type(universe, origin);
        if indices.is_empty() {
            return Ok(universe);
        }
        let dependent = dependence(indices, Tail::Results(&[]));
        let mut domains = Vec::with_capacity(indices.len());
        for (depth, binder) in indices.iter().enumerate() {
            let context = Context {
                binders: indices.get(.. depth).unwrap_or_default(),
                dependent: dependent.get(.. depth).unwrap_or_default(),
            };
            domains.push(self.sort_type(&binder.sort, context, minting, sink)?);
        }
        let mut chain = sink.arena.comp_type_returner(universe);
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
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_family_of_the_wrong_telescope_is_refused`
    /// - witness: `tests::modules::models::a_written_family_of_the_wrong_telescope_is_refused`
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
        let mut parameters = Vec::new();
        for (&slot, check) in self
            .collected
            .family_checks
            .range(SlotIndex::from(self.current.slots) ..)
        {
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
            parameters.clear();
            for parameter in &family.parameters {
                match self.value_type_at(parameter.classifier.node) {
                    Maybe::Present(id) => parameters.push(id),
                    Maybe::Absent(_) => break,
                }
            }
            if parameters.len() != family.parameters.len() {
                continue;
            }
            let indices = match check.stated {
                FamilyForm::Written(kind) => self.written_indices(kind, sink, origin),
                FamilyForm::Derived => {
                    self.derived_indices(check.structure, check.component, sink, origin)
                },
            };
            let indices = match indices {
                Ok(indices) => indices,
                Err(missing) => {
                    let refusal = match missing {
                        Missing::Refused(refusal) => refusal,
                        Missing::Unlowered => LoweringRefusal::UnreadAscription {
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
    /// - ensures: read through the parentheses around the kind as a whole, one
    ///   type per entry of the kind's domain — each entry of a parenthesised
    ///   list, the domain itself when written bare, or each domain along a
    ///   static arrow's spine — each carried into the context binding every
    ///   entry before it.
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
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::models::a_written_family_of_the_wrong_telescope_is_refused`
    /// - witness: `tests::modules::a_kinded_type_component_spine_declares_its_arity`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |types| types.iter().all(|&id| sink.arena.value_type(id).is_some())))]
    fn written_indices(
        &self,
        kind: Placed,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<Vec<ValueTypeId>, Missing<'source>>
    {
        let kind = ungrouped(self.pbg, self.tree, kind).map_err(Missing::Refused)?;
        if let Ok(Some((_, Former::ArrowType))) = self.form_at(kind) {
            let domains = spine_domains(self.pbg, self.tree, kind).map_err(Missing::Refused)?;
            let mut indices = Vec::with_capacity(domains.len());
            for domain in domains {
                let Maybe::Present(id) = self.value_type_at(domain.node)
                else {
                    return Err(Missing::Unlowered);
                };
                let frame = self.reading(domain.node).frame();
                indices.push(self.relocate_value_type(
                    id,
                    frame,
                    Telescope::Signature,
                    sink,
                    origin,
                ));
            }
            return Ok(indices);
        }
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, kind.node, &mut pieces).map_err(Missing::Refused)?;
        let Some(domain) = pieces.pieces.iter().find_map(|piece| match *piece {
            Piece::Operand(operand) => Some(operand),
            Piece::Tile { .. } => None,
        })
        else {
            return Err(Missing::Unlowered);
        };
        let entries: Vec<NodeIndex> = match self.form_at(domain) {
            Ok(Some((name, Former::ParenthesizedType))) => {
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
            Ok(_) => Vec::from([domain.node]),
            Err(refusal) => return Err(Missing::Refused(refusal)),
        };
        let mut indices = Vec::with_capacity(entries.len());
        for entry in entries {
            let Maybe::Present(id) = self.value_type_at(entry)
            else {
                return Err(Missing::Unlowered);
            };
            let frame = self.reading(entry).frame();
            indices.push(self.relocate_value_type(id, frame, Telescope::Signature, sink, origin));
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
    /// - witness: `tests::modules::models::a_family_of_the_wrong_telescope_is_refused`
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
            members: Members::Module {
                structure,
                operations: BTreeMap::new(),
            },
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
    /// - ensures: the kind's type and, for a static arrow — read through the
    ///   parentheses around the kind as a whole — `λ … λ. ⌜τ⌝`, one static
    ///   abstraction per parameter; otherwise `thunk (λ … λ. return ⌜τ⌝)`, one
    ///   lambda per parameter; every node carrying `origin`; nothing when the
    ///   kind or the family's type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the written `CatShape` family checks its member at
    ///   its kind, and a family read against a static arrow, bare or in
    ///   parentheses (#611), checks as an operator.
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
    /// - witness: `tests::modules::a_kind_reads_through_its_grouping_parentheses`
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
        let operator_kind = ungrouped(self.pbg, self.tree, kind).unwrap_or(kind);
        if let Ok(Some((_, Former::ArrowType))) = self.form_at(operator_kind) {
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

/// The value of the bundled record `signature` states, one value of `values`
/// per component in signature order.
///
/// # Specification
/// - requires: `values` holds one value per component of `signature`.
/// - ensures: the values nested to the right as the bundled record nests its
///   fields: the record keyed by the components' names when no field names
///   another, and otherwise the pair of each value and the rest, the last value
///   alone; the outermost node carrying `top` and every pair below it `below`;
///   nothing only for no values.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// The loop runs once per value but the last.
///
/// # Adequacy
/// - hypothesis: L3 — a counter's module packs as the pairs its record nests.
/// - witness: `tests::modules::models::a_manifest_module_packs_as_the_record_of_its_members`
#[spec(ensures: |ret| ret.is_some() || values.is_empty())]
fn packed_record(
    signature: &ModelSignature,
    values: &[ValueId],
    sink: &mut Sink<'_>,
    (top, below): (Origin, Origin),
) -> Option<ValueId>
{
    let binds = bundle_dependence(signature);
    if !binds.iter().any(|binds| binds.0) {
        let record = signature
            .components
            .iter()
            .zip(values)
            .map(|(component, &id)| (FieldLabel::from(String::from(component.name.as_ref())), id))
            .collect();
        let id = sink.arena.value_record(record);
        sink.origins.record_value(id, top);
        return Some(id);
    }
    let (&last, earlier) = values.split_last()?;
    let mut chained = last;
    for (link, &first) in earlier.iter().enumerate().rev() {
        chained = sink.arena.value_tuple(&[first, chained]);
        sink.origins
            .record_value(chained, if link == 0 { top } else { below });
    }

    Some(chained)
}

/// Whether each component of `signature` is named by a later one, and so its
/// link in the bundled record binds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one flag per component, in order: affirmative exactly when a
///   later component's sort terms name it or a later law's terms apply it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the toggle's carrier binds and its operations do not; a
///   law-bearing theory's operations bind.
/// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
/// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
#[spec(ensures: |ret| ret.len() == signature.components.len())]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `named` holds the names one signature's components read"
    )
)]
fn bundle_dependence(signature: &ModelSignature) -> Vec<Dependent>
{
    let mut named: Vec<&Name> = Vec::new();
    let mut flags = Vec::with_capacity(signature.components.len());
    for component in signature.components.iter().rev() {
        flags.push(Dependent(named.contains(&&component.name)));
        component_reads(component, &mut named);
    }
    flags.reverse();

    flags
}

/// Push every name `component` reads onto `into`: the sorts its sort terms
/// name and the operations its terms apply.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per sort term's sort and per application's head, in the
///   order the component states them.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`bundle_dependence`].
/// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
#[spec(
    captures: before = into.len(),
    ensures: into.len() >= before,
)]
fn component_reads<'form>(
    component: &'form ModelComponent,
    into: &mut Vec<&'form Name>,
)
{
    match component.form {
        Ok(ModelForm::Sort { ref indices }) => {
            for binder in indices {
                sort_reads(&binder.sort, into);
            }
        },
        Ok(ModelForm::Operation {
            ref telescope,
            ref results,
        }) => {
            for binder in telescope {
                sort_reads(&binder.sort, into);
            }
            for result in results {
                sort_reads(result, into);
            }
        },
        Ok(ModelForm::Constant(ref sort)) => sort_reads(sort, into),
        Ok(ModelForm::Law {
            ref telescope,
            ref carrier,
            ref left,
            ref right,
        }) => {
            for binder in telescope {
                sort_reads(&binder.sort, into);
            }
            sort_reads(carrier, into);
            term_heads(left, into);
            term_heads(right, into);
        },
        Ok(ModelForm::Nested(_)) | Err(_) => {},
    }
}

/// Push the sort `sort` names and the heads its index terms apply onto
/// `into`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the sort's name, then each index term's heads in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`bundle_dependence`].
/// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
#[spec(
    captures: before = into.len(),
    ensures: into.len() > before,
)]
fn sort_reads<'form>(
    sort: &'form SortTerm,
    into: &mut Vec<&'form Name>,
)
{
    into.push(&sort.sort);
    for index in &sort.indices {
        term_heads(index, into);
    }
}

/// Push the head of every application in `term` onto `into`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per operation application of the term.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Each node of the finite term is pushed once and popped once.
///
/// # Adequacy
/// - hypothesis: L3 — as [`bundle_dependence`].
/// - witness: `tests::modules::models::a_law_bearing_model_type_reads_its_operations`
#[spec(
    captures: before = into.len(),
    ensures: into.len() >= before,
)]
fn term_heads<'term>(
    term: &'term FreeTerm,
    into: &mut Vec<&'term Name>,
)
{
    let mut pending = Vec::from([term.to_node()]);
    while let Some(node) = pending.pop() {
        match node.view() {
            TermView::Var(_) => {},
            TermView::Op { name, args } => {
                into.push(name);
                pending.extend(args);
            },
            TermView::Ctor { args, .. }
            | TermView::Results { args }
            | TermView::Inst { args, .. }
            | TermView::Abs { args, .. } => {
                pending.extend(args);
            },
        }
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
/// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
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
