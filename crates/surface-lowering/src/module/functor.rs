//! Generative functors, as the collection pass reads them: the declaration
//! `module MkSet(Elt : #{ … }) :> #{ … } { … }`, collected once as a template,
//! and each application `module IntSet = MkSet(IntOrd) ;`, collected as an
//! instance of it. The minting half lives with the lowering
//! (`crate::lower::functor`).
//!
//! # A functor is a template the stratum binds, never a kernel term
//!
//! A functor declares no value. Its body is collected as a module's is, under
//! the functor's name: members, type members, nested modules, the result
//! ascription and, under `:>`, one abstract slot per abstract component. Its
//! parameter is collected beside it as a module with no body, whose
//! components stand for the argument's: an abstract component is a slot whose
//! position is the atom a reference `Elt.T` reads, a value component a slot
//! whose position a reference `Elt.x` reads, a manifest one the type it
//! states. A parameter written `(S : Model(T))` takes the components the
//! theory `T` derives, as a module ascribed `Model(T)` does: each unindexed
//! sort an abstract component, each operation and each law a value component
//! whose type the derivation mints, and an indexed sort refused as a written
//! family component is. Every one of those slots — parameter and body
//! alike — is a template slot: it lowers, so a refusal inside the functor is
//! reported where it was written, and it yields no declaration. The functor
//! is a thunk the stratum holds; nothing of it reaches the core or the kernel.
//!
//! An application forces the functor and applies it. The argument is matched
//! against the parameter as transparent ascription matches a module, by
//! component name, so a reordered or wider argument matches: each value
//! component is checked by a witness at the parameter's type, each abstract
//! component by a witness of its kind over the argument's type, each manifest
//! one by a witness that the argument's type is the one it states. A component
//! the argument does not export refuses the application under its name. The
//! instance is then the body's image: one module per module of the body, the
//! first named by the binding, and one slot per body slot, in the body's
//! order, after the witnesses. Its declarations are the template's renamed:
//! each body position to its image, each parameter atom to the argument's
//! type, each parameter value component to its witness, each of the body's
//! atoms to the image's. The image of an abstract slot is sealed at the
//! instance's own module, so its sealing site is the application's and every
//! application mints its own atoms: `module A = MkCounter(Seed) ;` and `module
//! B = MkCounter(Seed) ;` export two distinct types.
//!
//! - Choice: the parameter is strengthened at each application (Leroy's
//!   manifest types, the ML reading): an argument whose type is visible lends
//!   it to the instance, so sharing survives, and the body is checked at each
//!   instance rather than once against an abstract parameter. Alternatives:
//!   sealing the parameter, which loses sharing — an instance could not accept
//!   the argument's own values; checking the body once against the parameter's
//!   atoms, which needs declarations the checker reads and the kernel never
//!   sees. Reversal: separately elaborated functors, whose body must check
//!   before any application exists.
//! - Choice: an instance is the template renamed in the core, not the body
//!   lowered again. Alternatives: lowering the functor's syntax once per
//!   application, which the lowering's one reading per syntax node forbids.
//!   Reversal: none foreseen; the renaming is the substitution of the record.
//! - Choice: force-then-apply is elaborated here, in the modules region of the
//!   lowering, where the coercive matching of an ascription lives, and the
//!   checker receives each instance as declarations: its witnesses, then the
//!   body's image, every abstract slot of which the checker seals at its own
//!   site, so the seal is keyed by the application. Alternatives: a module term
//!   in the checker's modules region with its own force and apply, which would
//!   match signatures in two crates; checking a functor's body there once,
//!   which is the separately elaborated functor below. Reversal: functor bodies
//!   in the kernel, which would need the checker to hold the template as a
//!   term.
//!
//! # An application is a binding, and nothing projects from it
//!
//! The grammar writes an application only as a module binding, so
//! `MkCounter(Seed).T` names no instance: an application projected from is
//! refused by name, `ProjectionFromApplication`, and the instance it would
//! name is bound first, `module A = MkCounter(Seed) ;`, then read as `A.T`.
//!
//! # Held outside this rung
//!
//! A functor is declared and applied at the top level, over one parameter
//! signature, and every application is generative. Not built here: an
//! application whose argument's grades exhaust a parameter's, which the module
//! grades question decides; an application to a builtin model; applicative
//! functors, whose instances share atoms by their arguments' paths; functor
//! bodies in the kernel, which only ever sees instances; a functor whose body
//! performs effects, which waits for effectful module members; and a family
//! component of a functor's result, which an instance does not export until a
//! family's expansion renames with its instance.
//!
//! # References
//!
//! - Xavier Leroy. "Applicative Functors and Fully Transparent Higher-Order
//!   Modules." _POPL 1995_. <https://doi.org/10.1145/199448.199476>
//! - Derek Dreyer, Karl Crary and Robert Harper. "A Type System for
//!   Higher-Order Modules." _POPL 2003_. <https://doi.org/10.1145/604131.604151>
//! - Andreas Rossberg, Claudio Russo and Derek Dreyer. "F-ing Modules."
//!   _Journal of Functional Programming_ 24(5) (2014).
//!   <https://doi.org/10.1017/S0956796814000264>

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use super::Coerced;
use super::Collector;
use super::Component;
use super::ComponentForm;
use super::ComponentPlace;
use super::ComponentScope;
use super::Container;
use super::DeclarationSlot;
use super::Half;
use super::Member;
use super::ModelIndex;
use super::ModelPart;
use super::Operand;
use super::Role;
use super::Sealed;
use super::SlotIndex;
use super::Structure;
use super::StructureIndex;
use super::TypeComponent;
use super::TypeMeaning;
use super::component_kind;
use super::declaration_half;
use super::slot_refusal;
use crate::error::AscriptionForm;
use crate::error::LoweringRefusal;
use crate::form::Placed;
use crate::resolve::SurfaceName;

quenchant_shape::reason_enum! {
    /// Why a module form declares no functor parameter.
    pub mod parameter {
        /// The form is a module's, not a functor's.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `(X : #{ … })` follows the name.
            Unparameterized,
        }
    }
}

/// A functor's place in the collection's functor list.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctorIndex(pub usize);

impl From<FunctorIndex> for usize
{
    /// The place as a count of the functors before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: FunctorIndex) -> Self
    {
        index.0
    }
}

/// An application's place in the collection's instance list.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InstanceIndex(pub usize);

impl From<InstanceIndex> for usize
{
    /// The place as a count of the applications before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: InstanceIndex) -> Self
    {
        index.0
    }
}

/// What a collected module is in the stratum.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: a module, a functor's body or parameter, or an application's
///   instance, each naming its functor or application.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the indices are not checked against a collection.
///
/// # Adequacy
/// - hypothesis: L3 — a functor's body and parameter enter no namespace while
///   its instances do.
/// - witness: `tests::modules::functors::the_classic_functor_pair_checks`
/// - witness: `tests::modules::functors::a_functor_body_never_reaches_the_kernel`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stratum
{
    /// A module, or a module nested in one.
    #[default]
    Module,
    /// The body of this functor: the template its applications rename.
    Functor(FunctorIndex),
    /// The parameter of this functor.
    Parameter(FunctorIndex),
    /// The image of a functor's body this application binds.
    Instance(InstanceIndex),
}

/// A functor's parameter, as its header writes it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenParameter<'source>
{
    /// The parameter's name.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub named: Placed,
    /// The parameter signature's components, in signature order.
    pub components: Vec<Component<'source>>,
    /// The model signature a parameter written `(S : Model(T))` derives from
    /// `T`, or why none: a record signature states its components itself.
    pub model: Maybe<crate::model::ModelSignature, super::derived::Absent>,
}

/// What one parameter component stands for in the template.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: a value component carries its written type, an abstract one its
///   written kind, a manifest one the type it states; each is held by its
///   template slot.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the record holds no tree to check the nodes against.
///
/// # Adequacy
/// - hypothesis: L3 — a functor over an abstract type and a value of it applies
///   to a sealed argument.
/// - witness: `tests::modules::functors::the_classic_functor_pair_checks`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ParameterForm
{
    /// A value component `x : τ`, with its type.
    Value(Placed),
    /// An abstract component `type T` or `type T : κ`, with its kind.
    Abstract(Maybe<Placed, component_kind::Absent>),
    /// A manifest component `type T = τ`, with the type it states.
    Manifest(Placed),
    /// An operation or a law of a parameter's `Model(S)`, at its place in the
    /// model signature `S` derives, which mints its type.
    Derived(ModelPart),
}

/// One component of a functor's parameter, with its template slot.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ParameterComponent<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub named: Placed,
    /// The slot standing for it in the template: the atom an abstract
    /// component reads, the constant a value component reads, the held slot
    /// owning a manifest one's type.
    pub slot: SlotIndex,
    /// What it states.
    pub form: ParameterForm,
}

/// A functor as the collection found it: a template the stratum holds.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: the parameter's slots precede the body's, and the body's run from
///   `body_first` to `end`, its nested modules' included; the template modules
///   run from the body's index to `structures_end`.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the ranges are not checked against a collection.
///
/// # Adequacy
/// - hypothesis: L3 — a functor's template slots yield no declaration and each
///   application's image mirrors its body.
/// - witness: `tests::modules::functors::a_functor_body_never_reaches_the_kernel`
/// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Functor<'source>
{
    /// The functor's name.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub named: Placed,
    /// The functor form.
    pub declared_by: Placed,
    /// The parameter's name.
    pub parameter_name: SurfaceName<'source>,
    /// The parameter, collected as a module with no body.
    pub parameter: StructureIndex,
    /// The body, collected as a module.
    pub body: StructureIndex,
    /// The parameter's components, in signature order.
    pub components: Vec<ParameterComponent<'source>>,
    /// The template's first slot: the parameter's first.
    pub first: SlotIndex,
    /// The body's first slot, past the parameter's.
    pub body_first: SlotIndex,
    /// The slot past the template's last.
    pub end: SlotIndex,
    /// The module past the template's last.
    pub structures_end: StructureIndex,
}

/// What the instance matched one parameter component with.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: every form carries the parameter's template slot and the witness
///   checking the argument against it; a value component the argument's member
///   a reference reads, a type component what the argument's type reads.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the indices are not checked against a collection.
///
/// # Adequacy
/// - hypothesis: L3 — a value component of the argument at the parameter's type
///   checks and one at another type is refused at its witness.
/// - witness: `tests::modules::functors::the_classic_functor_pair_checks`
/// - witness: `tests::modules::functors::an_argument_is_matched_against_the_parameter`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Matched<'source>
{
    /// A value component, checked at the parameter's type by `witness`,
    /// whose body is the argument's member at `member`.
    Value
    {
        /// The parameter's slot.
        parameter: SlotIndex,
        /// The witness.
        witness: SlotIndex,
        /// The argument's member a reference reads.
        member: SlotIndex,
    },
    /// An abstract type component, whose argument's type `witness` checks at
    /// the parameter's kind.
    Abstract
    {
        /// The parameter's atom.
        parameter: SlotIndex,
        /// The witness.
        witness: SlotIndex,
        /// The argument's type component.
        argument: TypeComponent<'source>,
    },
    /// A manifest type component, whose argument's type `witness` checks is
    /// the type the parameter states.
    Manifest
    {
        /// The held slot owning the parameter's type.
        parameter: SlotIndex,
        /// The witness.
        witness: SlotIndex,
        /// The argument's type component.
        argument: TypeComponent<'source>,
    },
}

/// One application, as the collection found it.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: the instance's module is the body's image; the witnesses precede
///   the body's image, whose slots run from `body_first` in the body's order;
///   `images` maps each module of the body to its image.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the indices are not checked against a collection.
///
/// # Adequacy
/// - hypothesis: L3 — two applications of one functor to one argument bind two
///   instances, each with its own atoms.
/// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Instance<'source>
{
    /// The binding's name.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub named: Placed,
    /// The binding form.
    pub declared_by: Placed,
    /// The functor applied.
    pub functor: FunctorIndex,
    /// The argument module.
    pub argument: StructureIndex,
    /// The instance's module: the image of the functor's body.
    pub structure: StructureIndex,
    /// What each parameter component matched, in signature order.
    pub matched: Vec<Matched<'source>>,
    /// The first slot of the body's image.
    pub body_first: SlotIndex,
    /// Each module of the functor's body, with its image.
    pub images: BTreeMap<StructureIndex, StructureIndex>,
}

impl Instance<'_>
{
    /// The image of the template slot `slot` of `functor`, the functor this
    /// instance applies.
    ///
    /// # Specification
    /// - requires: `functor` is the functor this instance applies.
    /// - ensures: for a slot of the functor's body, the slot as many positions
    ///   past the image's first as it is past the body's first; absent for any
    ///   other slot.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Instance`].
    /// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(image) => functor.body_first <= slot && slot < functor.end
            && usize::from(image).checked_sub(usize::from(self.body_first)) == usize::from(slot).checked_sub(usize::from(functor.body_first)),
        | Maybe::Absent(_) => slot < functor.body_first || slot >= functor.end,
    })]
    #[inline]
    pub fn image(
        &self,
        functor: &Functor<'_>,
        slot: SlotIndex,
    ) -> Maybe<SlotIndex, image::Absent>
    {
        if slot >= functor.end {
            return Maybe::Absent(image::Absent::Outside);
        }
        let Some(offset) = usize::from(slot).checked_sub(usize::from(functor.body_first))
        else {
            return Maybe::Absent(image::Absent::Outside);
        };
        usize::from(self.body_first)
            .checked_add(offset)
            .map_or(Maybe::Absent(image::Absent::Outside), |at| {
                Maybe::Present(SlotIndex::from(at))
            })
    }
}

quenchant_shape::reason_enum! {
    /// Why a slot has no image in an instance.
    pub mod image {
        /// The slot is not one of the functor's body.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The slot is the parameter's, or no template slot at all.
            Outside,
        }
    }
}

/// An application as its header writes it: `module A = F(P) ;`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Applied<'source>
{
    /// The binding's name.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub named: Placed,
    /// The functor's name tile.
    pub functor: Placed,
    /// The argument's path, one tile per segment.
    pub argument: Vec<Placed>,
}

impl<'source> Collector<'_, 'source>
{
    /// Collect the parameter of the functor whose body is the module just
    /// opened at `body`, and record the functor.
    ///
    /// # Specification
    /// - requires: `body` was just pushed and holds no slot yet.
    /// - ensures: the parameter is the next module, nested in the body under
    ///   its own name, ascribed by its signature and carrying the model a
    ///   `Model(S)` parameter derives; each component takes a
    ///   [`Role::Parameter`] slot in signature order — an abstract one owning
    ///   its written kind, a value one owning its type, which sees the
    ///   parameter's earlier type components, a derived one stated by its place
    ///   in the model — and a manifest one a held slot owning its type; a
    ///   family or an unread component refuses a held slot under its name; the
    ///   body is marked as the functor's and the functor is recorded, its
    ///   body's first slot past the parameter's.
    /// - provides: the parameter half of a functor's collection.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter of an abstract type and a value of it is
    ///   read by the body at its atom and its constant.
    /// - witness: `tests::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `tests::modules::functors::a_functor_over_a_model_applies_to_one_1226`
    #[spec(
        captures: before = (self.collected.functors.len(), self.collected.structures.len()),
        ensures: self.collected.functors.len() == before.0.saturating_add(1)
            && self.collected.structures.len() == before.1.saturating_add(1)
            && self.collected.structures.get(body.0).is_some_and(|entry| entry.stratum == Stratum::Functor(FunctorIndex(before.0))),
    )]
    pub(super) fn declare_parameter(
        &mut self,
        body: StructureIndex,
        written: WrittenParameter<'source>,
    )
    {
        let functor = FunctorIndex(self.collected.functors.len());
        let parameter = StructureIndex(self.collected.structures.len());
        let first = SlotIndex(self.collected.slots.len());
        let container = Container::Module(parameter);
        let components = written.components.clone();
        let model = written.model.map(|derived| {
            let index = ModelIndex(self.collected.models.len());
            self.collected.models.push(derived);
            index
        });
        self.collected.structures.push(Structure {
            name: written.name,
            container: Container::Module(body),
            declared_by: written.named,
            named: written.named,
            ascription: Maybe::Present(written.components),
            model,
            sealed: Sealed(true),
            members: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            type_members: Vec::new(),
            exported_as: BTreeMap::new(),
            stated_at: Vec::new(),
            coerced: Coerced(true),
            stratum: Stratum::Parameter(functor),
        });
        let _fresh = self
            .collected
            .modules
            .insert((Container::Module(body), written.name), parameter);
        let mut stated = Vec::new();
        let mut types: Vec<TypeComponent<'source>> = Vec::new();
        let mut exports = Vec::new();
        for (place, component) in components.into_iter().enumerate() {
            let scope = ComponentScope {
                structure: parameter,
                before: types.len(),
            };
            let form = match component.form {
                ComponentForm::Value(typed) => ParameterForm::Value(typed),
                ComponentForm::Abstract(Maybe::Present(kind))
                    if matches!(self.kind_form(kind), Ok(super::sealing::KindForm::Arrow)) =>
                {
                    self.refuse_component(container, component, AscriptionForm::Kinded);
                    continue;
                },
                ComponentForm::Abstract(kind) => ParameterForm::Abstract(kind),
                ComponentForm::Manifest(defined) => ParameterForm::Manifest(defined),
                ComponentForm::Derived => match model {
                    Maybe::Present(index) => ParameterForm::Derived(ModelPart {
                        model: index,
                        component: ComponentPlace(place),
                    }),
                    Maybe::Absent(_) => {
                        self.refuse_component(container, component, AscriptionForm::Kinded);
                        continue;
                    },
                },
                ComponentForm::Family(_) => {
                    self.refuse_component(container, component, AscriptionForm::Kinded);
                    continue;
                },
                ComponentForm::Parameterized { .. } => {
                    self.refuse_component(container, component, AscriptionForm::Parameterized);
                    continue;
                },
                ComponentForm::Unread(form) => {
                    self.refuse_component(container, component, form);
                    continue;
                },
            };
            let slot = match form {
                ParameterForm::Manifest(defined) => {
                    let held =
                        self.held(container, component.name, component.named, component.named);
                    self.collected.own(defined.node, held);
                    self.collected.scopes.push((defined.node, scope));
                    types.push(TypeComponent {
                        name: component.name,
                        meaning: TypeMeaning::Manifest(defined),
                        held,
                    });
                    held
                },
                ParameterForm::Value(typed) => {
                    let slot = self.parameter_slot(container, component, Maybe::Present(typed));
                    self.collected.own(typed.node, slot);
                    self.collected.scopes.push((typed.node, scope));
                    exports.push(Member::Slot(slot));
                    slot
                },
                ParameterForm::Derived(part) => {
                    let slot = self.parameter_slot(
                        container,
                        component,
                        Maybe::Absent(declaration_half::Absent::Unwritten),
                    );
                    self.state(
                        slot,
                        Operand::Model(part),
                        component.named,
                        Maybe::Present(scope),
                    );
                    exports.push(Member::Slot(slot));
                    slot
                },
                ParameterForm::Abstract(kind) => {
                    let slot = self.parameter_slot(
                        container,
                        component,
                        Maybe::Absent(declaration_half::Absent::Unwritten),
                    );
                    if let Maybe::Present(written_kind) = kind {
                        self.collected.own(written_kind.node, slot);
                    }
                    types.push(TypeComponent {
                        name: component.name,
                        meaning: TypeMeaning::Sealed,
                        held: slot,
                    });
                    slot
                },
            };
            stated.push(ParameterComponent {
                name: component.name,
                named: component.named,
                slot,
                form,
            });
        }
        if let Some(entry) = self.collected.structures.get_mut(parameter.0) {
            entry.members.clone_from(&exports);
            entry.exports = exports;
            entry.types = types;
        }
        if let Some(entry) = self.collected.structures.get_mut(body.0) {
            entry.stratum = Stratum::Functor(functor);
        }
        let (name, named, declared_by) = self
            .collected
            .structures
            .get(body.0)
            .map_or((written.name, written.named, written.named), |entry| {
                (entry.name, entry.named, entry.declared_by)
            });
        let body_first = SlotIndex(self.collected.slots.len());
        self.collected.functors.push(Functor {
            name,
            named,
            declared_by,
            parameter_name: written.name,
            parameter,
            body,
            components: stated,
            first,
            body_first,
            end: body_first,
            structures_end: StructureIndex(self.collected.structures.len()),
        });
    }

    /// A [`Role::Parameter`] slot for `component` in `container`, its written
    /// type the signature half when it has one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot takes the next admission position, named and
    ///   introduced by the component's name, with `typed` as its signature
    ///   written at the name and no definition, and is entered in no name
    ///   table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::declare_parameter`].
    /// - witness: `tests::modules::functors::the_classic_functor_pair_checks`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| ret.0 == before && self.collected.slots.len() == before.saturating_add(1)
            && self.collected.slots.get(before).is_some_and(|slot| slot.role == Role::Parameter && slot.container == container),
    )]
    fn parameter_slot(
        &mut self,
        container: Container,
        component: Component<'source>,
        typed: Maybe<Placed, declaration_half::Absent>,
    ) -> SlotIndex
    {
        let minted = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name: component.name,
            container,
            role: Role::Parameter,
            constant: ConstantIndex::from(minted.0),
            introduced_by: component.named,
            named: component.named,
            signature: typed.map(|operand| Half {
                declaration: component.named,
                named: component.named,
                operand: Operand::Written(operand),
            }),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });

        minted
    }

    /// Refuse the parameter component `component`, whose form the parameter
    /// does not read, under its name in `container`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one held slot carries [`LoweringRefusal::UnreadAscription`]
    ///   naming the component and `form`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family component of a parameter is refused at its
    ///   name.
    /// - witness: `tests::modules::functors::a_parameter_reads_only_types_and_values`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: self.collected.slots.len() == before.saturating_add(1),
    )]
    fn refuse_component(
        &mut self,
        container: Container,
        component: Component<'source>,
        form: AscriptionForm,
    )
    {
        let refusal = LoweringRefusal::UnreadAscription {
            span: component.named.span,
            name: component.name,
            form,
        };
        let _held = self.refuse_held(
            container,
            component.name,
            component.named,
            component.named,
            refusal,
        );
    }

    /// Close the functor whose body is the top-level module at `body`, once
    /// every module nested in it has closed.
    ///
    /// # Specification
    /// - requires: the body's collection, nested modules included, is done.
    /// - ensures: a functor's body fixes the template's end at the slots and
    ///   modules taken so far; any other module changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a functor's template slots yield no declaration.
    /// - witness: `tests::modules::functors::a_functor_body_never_reaches_the_kernel`
    #[spec(
        captures: before = self.collected.functors.len(),
        ensures: self.collected.functors.len() == before,
    )]
    pub(super) fn close_functor(
        &mut self,
        body: StructureIndex,
    )
    {
        let Some(&Structure {
            stratum: Stratum::Functor(functor),
            ..
        }) = self.collected.structures.get(body.0)
        else {
            return;
        };
        let end = SlotIndex(self.collected.slots.len());
        let structures_end = StructureIndex(self.collected.structures.len());
        if let Some(entry) = self.collected.functors.get_mut(functor.0) {
            entry.end = end;
            entry.structures_end = structures_end;
        }
    }

    /// Collect the application `applied`, written by the form `form`.
    ///
    /// # Specification
    /// - requires: `applied` is the header of the top-level form `form`.
    /// - ensures: a binding whose name a module already takes, whose functor
    ///   names no functor declared before it, whose argument names no module,
    ///   or whose argument misses a component of the parameter refuses a held
    ///   slot under the binding's name; otherwise the instance is the next
    ///   module, under the binding's name, its witnesses the next slots, then
    ///   the image of every module and every slot of the functor's body, in the
    ///   body's order, each module mapped as its template is.
    /// - provides: the collection half of an application.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two applications bind two instances, and an argument
    ///   missing a component refuses its binding.
    /// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
    /// - witness: `tests::modules::functors::an_argument_is_matched_against_the_parameter`
    #[spec(
        captures: before = (self.collected.instances.len(), self.collected.slots.len()),
        ensures: self.collected.instances.len() <= before.0.saturating_add(1)
            && self.collected.slots.len() > before.1,
    )]
    pub(super) fn apply(
        &mut self,
        form: Placed,
        applied: &Applied<'source>,
    )
    {
        let top = self.collected.top(form.span.start());
        let refuse = |collector: &mut Self, refusal| {
            let _held = collector.refuse_held(top, applied.name, form, applied.named, refusal);
        };
        if let Some(&first) = self.collected.modules.get(&(top, applied.name)) {
            let first = self
                .collected
                .structures
                .get(first.0)
                .map_or(form.span, |earlier| earlier.named.span);
            refuse(self, LoweringRefusal::DuplicateDefinition {
                span: applied.named.span,
                name: applied.name,
                first,
            });
            return;
        }
        let functor_name = self.name_of(applied.functor);
        let Some((functor, template)) = self
            .collected
            .functors
            .iter()
            .enumerate()
            .find(|&(_, functor)| functor.name == functor_name)
            .map(|(index, functor)| (FunctorIndex(index), functor.clone()))
        else {
            refuse(self, LoweringRefusal::NotAFunctor {
                span: applied.functor.span,
                name: functor_name,
            });
            return;
        };
        let Some((&head, rest)) = applied.argument.split_first()
        else {
            refuse(self, LoweringRefusal::UnresolvedName {
                span: applied.functor.span,
                name: functor_name,
            });
            return;
        };
        let argument = match self.argument(head, rest) {
            Ok(argument) => argument,
            Err(refusal) => {
                refuse(self, refusal);
                return;
            },
        };
        let argument_name = applied
            .argument
            .last()
            .map_or(functor_name, |&last| self.name_of(last));
        let argument_span = applied
            .argument
            .last()
            .map_or(applied.functor.span, |last| last.span);
        let mut found = Vec::new();
        for component in &template.components {
            match self.argument_component(argument, component) {
                Maybe::Present(argued) => found.push(argued),
                Maybe::Absent(_) => {
                    refuse(self, LoweringRefusal::UnknownMember {
                        span: argument_span,
                        module: argument_name,
                        member: component.name,
                    });
                    return;
                },
            }
        }
        self.instantiate(form, applied, functor, &template, argument, &found);
    }

    /// The module the argument path `head`, then `rest`, names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the top-level module or instance `head` names, then each
    ///   nested module the next segment names among its exports.
    /// - fails: [`LoweringRefusal::UnresolvedName`] for a head no module or
    ///   instance takes, functors' included; [`LoweringRefusal::UnknownMember`]
    ///   for a later segment its module does not export as a module.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an argument naming a sealed module and one naming no
    ///   module.
    /// - witness: `tests::modules::functors::the_classic_functor_pair_checks`
    /// - witness: `tests::modules::functors::an_argument_is_matched_against_the_parameter`
    /// - witness: `tests::modules::functors::an_argument_naming_a_functor_is_unresolved`
    /// - witness: `tests::modules::functors::a_dotted_argument_reads_the_nested_module_it_names`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.0 < self.collected.structures.len()))]
    fn argument(
        &self,
        head: Placed,
        rest: &[Placed],
    ) -> Result<StructureIndex, LoweringRefusal<'source>>
    {
        let head_name = self.name_of(head);
        let mut current = match self
            .collected
            .modules
            .get(&(self.collected.top(head.span.start()), head_name))
            .copied()
        {
            Some(found)
                if self.collected.structures.get(found.0).is_some_and(|entry| {
                    matches!(entry.stratum, Stratum::Module | Stratum::Instance(_))
                }) =>
            {
                found
            },
            Some(_) | None => {
                return Err(LoweringRefusal::UnresolvedName {
                    span: head.span,
                    name: head_name,
                });
            },
        };
        let mut previous = head_name;
        for &segment in rest {
            let name = self.name_of(segment);
            let nested = self.collected.structures.get(current.0).and_then(|entry| {
                entry.exports.iter().find_map(|&export| match export {
                    Member::Module(nested)
                        if self
                            .collected
                            .structures
                            .get(nested.0)
                            .is_some_and(|module| module.name == name) =>
                    {
                        Some(nested)
                    },
                    Member::Module(_) | Member::Slot(_) => None,
                })
            });
            let Some(nested) = nested
            else {
                return Err(LoweringRefusal::UnknownMember {
                    span: segment.span,
                    module: previous,
                    member: name,
                });
            };
            current = nested;
            previous = name;
        }

        Ok(current)
    }

    /// What the argument at `argument` exports for the parameter component
    /// `component`.
    ///
    /// # Specification
    /// - ensures: for a value or a derived component, the argument's exported
    ///   value member of its name, read through the witness a sealed argument
    ///   exports in its place; for a type component, the argument's exported
    ///   type component of its name that reads a type; absent otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an argument exporting every component and one missing
    ///   one.
    /// - witness: `tests::modules::functors::an_argument_is_matched_against_the_parameter`
    /// - witness: `tests::modules::functors::a_type_component_binds_the_argument_type_of_its_own_name`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(Argued::Value(slot)) => matches!(component.form, ParameterForm::Value(_) | ParameterForm::Derived(_)) && slot.0 < self.collected.slots.len(),
        | Maybe::Present(Argued::Type(found)) => !matches!(component.form, ParameterForm::Value(_) | ParameterForm::Derived(_)) && found.name == component.name,
        | Maybe::Absent(_) => true,
    })]
    fn argument_component(
        &self,
        argument: StructureIndex,
        component: &ParameterComponent<'source>,
    ) -> Maybe<Argued<'source>, argued::Absent>
    {
        let Some(entry) = self.collected.structures.get(argument.0)
        else {
            return Maybe::Absent(argued::Absent::Unexported);
        };
        match component.form {
            ParameterForm::Value(_) | ParameterForm::Derived(_) => entry
                .exports
                .iter()
                .find_map(|&export| match export {
                    Member::Slot(slot)
                        if self
                            .collected
                            .slots
                            .get(slot.0)
                            .is_some_and(|member| member.name == component.name) =>
                    {
                        Some(Argued::Value(
                            entry.exported_as.get(&slot).copied().unwrap_or(slot),
                        ))
                    },
                    Member::Slot(_) | Member::Module(_) => None,
                })
                .map_or(Maybe::Absent(argued::Absent::Unexported), Maybe::Present),
            ParameterForm::Abstract(_) | ParameterForm::Manifest(_) => entry
                .exported_types()
                .iter()
                .find(|stated| {
                    stated.name == component.name
                        && !matches!(stated.meaning, TypeMeaning::Family(_))
                })
                .map_or(Maybe::Absent(argued::Absent::Unexported), |&stated| {
                    Maybe::Present(Argued::Type(stated))
                }),
        }
    }

    /// Bind the instance of `template`, the functor at `functor`, applied to
    /// the module at `argument`, whose components are `found`.
    ///
    /// # Specification
    /// - requires: `found` holds one entry per parameter component, in order.
    /// - ensures: as [`Self::apply`] for a matched argument.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::apply`].
    /// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
    /// - witness: `tests::modules::functors::a_functor_body_never_reaches_the_kernel`
    #[spec(
        captures: before = (self.collected.instances.len(), self.collected.structures.len()),
        ensures: self.collected.instances.len() == before.0.saturating_add(1)
            && self.collected.structures.len() > before.1,
    )]
    fn instantiate(
        &mut self,
        form: Placed,
        applied: &Applied<'source>,
        functor: FunctorIndex,
        template: &Functor<'source>,
        argument: StructureIndex,
        found: &[Argued<'source>],
    )
    {
        let index = InstanceIndex(self.collected.instances.len());
        let structure = StructureIndex(self.collected.structures.len());
        let Some(body) = self.collected.structures.get(template.body.0).cloned()
        else {
            return;
        };
        self.collected.structures.push(Structure {
            name: applied.name,
            container: self.collected.top(form.span.start()),
            declared_by: form,
            named: applied.named,
            ascription: body.ascription.clone(),
            model: body.model,
            sealed: body.sealed,
            members: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            type_members: Vec::new(),
            exported_as: BTreeMap::new(),
            stated_at: Vec::new(),
            coerced: body.coerced,
            stratum: Stratum::Instance(index),
        });
        let _fresh = self.collected.modules.insert(
            (self.collected.top(form.span.start()), applied.name),
            structure,
        );
        let container = Container::Module(structure);
        let mut matched = Vec::with_capacity(found.len());
        for (component, &argued) in template.components.iter().zip(found) {
            let paired = match (component.form, argued) {
                (ParameterForm::Value(_) | ParameterForm::Derived(_), Argued::Value(member)) => {
                    Paired::Value(member)
                },
                (ParameterForm::Abstract(_), Argued::Type(stated)) => Paired::Abstract(stated),
                (ParameterForm::Manifest(_), Argued::Type(stated)) => Paired::Manifest(stated),
                (ParameterForm::Value(_) | ParameterForm::Derived(_), Argued::Type(_))
                | (ParameterForm::Abstract(_) | ParameterForm::Manifest(_), Argued::Value(_)) => {
                    continue;
                },
            };
            let witness = self.witness_slot(container, component.name, component.named, form);
            let parameter = component.slot;
            matched.push(match paired {
                Paired::Value(member) => Matched::Value {
                    parameter,
                    witness,
                    member,
                },
                Paired::Abstract(argument) => Matched::Abstract {
                    parameter,
                    witness,
                    argument,
                },
                Paired::Manifest(argument) => Matched::Manifest {
                    parameter,
                    witness,
                    argument,
                },
            });
        }
        let mut images = BTreeMap::from([(template.body, structure)]);
        for nested in template.body.0.saturating_add(1) .. template.structures_end.0 {
            let Some(entry) = self.collected.structures.get(nested).cloned()
            else {
                continue;
            };
            if entry.stratum != Stratum::Module {
                continue;
            }
            let container = match entry.container {
                Container::Module(parent) => images
                    .get(&parent)
                    .map_or(entry.container, |&image| Container::Module(image)),
                Container::TopLevel(_) => self.collected.top(form.span.start()),
            };
            let image = StructureIndex(self.collected.structures.len());
            self.collected.structures.push(Structure {
                container,
                members: Vec::new(),
                exports: Vec::new(),
                types: Vec::new(),
                type_members: Vec::new(),
                exported_as: BTreeMap::new(),
                stated_at: Vec::new(),
                ..entry
            });
            let _fresh = images.insert(StructureIndex(nested), image);
        }
        let body_first = SlotIndex(self.collected.slots.len());
        let instance = Instance {
            name: applied.name,
            named: applied.named,
            declared_by: form,
            functor,
            argument,
            structure,
            matched,
            body_first,
            images,
        };
        for template_slot in template.body_first.0 .. template.end.0 {
            let Some(slot) = self.collected.slots.get(template_slot).cloned()
            else {
                continue;
            };
            let container = match slot.container {
                Container::Module(owner) => instance
                    .images
                    .get(&owner)
                    .map_or(slot.container, |&image| Container::Module(image)),
                Container::TopLevel(_) => self.collected.top(form.span.start()),
            };
            let minted = SlotIndex(self.collected.slots.len());
            self.collected.slots.push(DeclarationSlot {
                name: slot.name,
                container,
                role: slot.role,
                constant: ConstantIndex::from(minted.0),
                introduced_by: form,
                named: slot.named,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Absent(declaration_half::Absent::Unwritten),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            });
        }
        let slot_image = |slot: SlotIndex| match instance.image(template, slot) {
            Maybe::Present(image) => image,
            Maybe::Absent(_) => slot,
        };
        let member_image = |member: Member| match member {
            Member::Slot(slot) => Member::Slot(slot_image(slot)),
            Member::Module(module) => {
                Member::Module(instance.images.get(&module).copied().unwrap_or(module))
            },
        };
        let type_image = |stated: &TypeComponent<'source>| match stated.meaning {
            TypeMeaning::Family(_) => None,
            TypeMeaning::Manifest(defined) => Some(TypeComponent {
                name: stated.name,
                meaning: TypeMeaning::Instantiated {
                    defined,
                    instance: index,
                },
                held: slot_image(stated.held),
            }),
            TypeMeaning::Sealed | TypeMeaning::Instantiated { .. } => Some(TypeComponent {
                name: stated.name,
                meaning: stated.meaning,
                held: slot_image(stated.held),
            }),
        };
        for (&template_module, &image) in &instance.images {
            let Some(entry) = self.collected.structures.get(template_module.0).cloned()
            else {
                continue;
            };
            if let Some(mirror) = self.collected.structures.get_mut(image.0) {
                mirror.members = entry.members.iter().copied().map(member_image).collect();
                mirror.exports = entry.exports.iter().copied().map(member_image).collect();
                mirror.types = entry.types.iter().filter_map(type_image).collect();
                mirror.type_members = entry.type_members.iter().filter_map(type_image).collect();
                mirror.exported_as = entry
                    .exported_as
                    .iter()
                    .map(|(&member, &read)| (slot_image(member), slot_image(read)))
                    .collect();
            }
        }
        self.collected.instances.push(instance);
    }

    /// A witness slot named `name` in `container`, checking one parameter
    /// component at an application written by `form`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot takes the next admission position as a
    ///   [`Role::Witness`] holding no half, named at the component's name and
    ///   introduced by the application, and is entered in no name table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::apply`].
    /// - witness: `tests::modules::functors::an_argument_is_matched_against_the_parameter`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| ret.0 == before && self.collected.slots.len() == before.saturating_add(1),
    )]
    fn witness_slot(
        &mut self,
        container: Container,
        name: SurfaceName<'source>,
        named: Placed,
        form: Placed,
    ) -> SlotIndex
    {
        let minted = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name,
            container,
            role: Role::Witness,
            constant: ConstantIndex::from(minted.0),
            introduced_by: form,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });

        minted
    }
}

/// What an argument exports for one parameter component.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Argued<'source>
{
    /// The member a reference to a value component reads.
    Value(SlotIndex),
    /// The type component a reference to a type component reads.
    Type(TypeComponent<'source>),
}

quenchant_shape::reason_enum! {
    /// Why an argument supplies no component of a name.
    mod argued {
        /// The argument does not export it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(super) enum Absent {
            /// No exported component of the argument bears the name at the
            /// sort the parameter states.
            Unexported,
        }
    }
}

/// One parameter component paired with what the argument supplies for it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Paired<'source>
{
    /// A value component, read at the argument's member.
    Value(SlotIndex),
    /// An abstract type component, read at the argument's type.
    Abstract(TypeComponent<'source>),
    /// A manifest type component, checked against the argument's type.
    Manifest(TypeComponent<'source>),
}
