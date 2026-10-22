//! Type members and abstract components, as the collection pass reads them,
//! and what an opaque ascription declares for them.
//!
//! # A body states a type by member, a signature hides it by component
//!
//! A module body declares a type member `type T = τ ;` beside its value
//! members. It declares nothing at the admission position its held slot
//! takes: `τ` is lowered once, owned by that slot, which carries its refusal,
//! and every reference to `T` adopts the type it lowered to — a later member
//! of the module or of one nested in it, by the bare name, and a client
//! through the namespace, by the path `M.T` when the module exports it. The
//! position stays skipped, so whatever reads the declarations by position
//! keys them by position rather than by their place in the list. A
//! signature's abstract component `type T` or `type T : κ` takes its meaning
//! from the body's type member of its name, and the ascription decides what
//! that meaning is outside.
//!
//! - Choice: the representation is written once, as a member, and the component
//!   names it by name. Alternatives: a witness list on the seal (`:> [Integer]
//!   #{ type T, … }`), which separates a type's definition from the module that
//!   uses it; inferring the representation from the members' types, which
//!   guesses and leaves a component no member mentions undetermined. Reversal:
//!   a different signature spelling moves the member form, nothing else.
//!
//! # An opaque ascription declares one abstract type per abstract component
//!
//! Under `:>` each abstract component becomes an [`Role::Abstract`] slot,
//! admitted when the module opens, before any member, so every member and
//! every witness of the module sits after it. The slot's declaration carries
//! the component's kind (the fuss-free universe `Type` when none is written),
//! the body member's type as its representation, the extent of its seal —
//! the positions from the slot through the module's last, fixed when the
//! module closes — and its site: the module's index in the pre-order of
//! modules and the component's place in the signature, never a name. The
//! checker mints one atom per site and reads the atom as its representation
//! for exactly the declarations the extent reaches; past it, the atom relates
//! to nothing but itself.
//!
//! The signature's later components, and every client through `M.T`, read the
//! atom, so a member stated at `T` is checked at the representation inside
//! and exported at the atom. A member that keeps a written type of its own is
//! exported through the witness that states the component's type, so the
//! member's own type does not leak past the seal (`Structure::exported_as`).
//!
//! - Choice: generative atoms keyed by site (Harper and Lillibridge's
//!   translucent sums, Leroy's manifest types). Alternatives: existential
//!   packing at the ascription, whose identity no importer can recheck; an atom
//!   per component name, which conflates two ascriptions of one name. Reversal:
//!   sealing across separately elaborated programs, where a site needs a
//!   component beyond the program's own numbering.
//!
//! # A transparent ascription strengthens
//!
//! Under `:` an abstract component reads as the body member's type itself,
//! so the identity the module's own type determines survives the ascription.
//! The kind the component states — `Type` when none is written — is checked
//! by a witness declaration at the kind whose body is the member's code, so
//! `type T : Type[+, 0]` over a member at a higher universe is refused as the
//! checker refuses any code above its universe.
//!
//! - Choice: the strengthened reading, with the kind kept as a check.
//!   Alternatives: minting an atom under `:` too, which makes every transparent
//!   ascription a sealing site; dropping the kind, which accepts a member the
//!   signature does not classify. Reversal: a transparent ascription that must
//!   hide a component, which is what `:>` is for.
//!
//! A kind written as a telescope Π into a universe, `type Hom : (a : Ob, b :
//! Ob) => Type`, declares a type family, matched against a family member
//! (`super::model`); a kind written as an arrow, `Ob -> Ob -> Type`, declares
//! the same family under a transparent ascription, its member checked at the
//! arrow as an operator over codes, and is refused under `:>` as
//! [`AscriptionForm::Kinded`]: an opaque operator would be an atom at a kind
//! no universe is.
//!
//! # References
//!
//! - Robert Harper and Mark Lillibridge. "A Type-Theoretic Approach to
//!   Higher-Order Modules with Sharing." _POPL 1994_.
//!   <https://doi.org/10.1145/174675.176927>
//! - Xavier Leroy. "Manifest Types, Modules, and Separate Compilation." _POPL
//!   1994_. <https://doi.org/10.1145/174675.176926>
//! - Derek Dreyer, Karl Crary and Robert Harper. "A Type System for
//!   Higher-Order Modules." _POPL 2003_. <https://doi.org/10.1145/604131.604151>
//! - Andreas Rossberg, Claudio Russo and Derek Dreyer. "F-ing Modules."
//!   _Journal of Functional Programming_ 24(5) (2014).
//!   <https://doi.org/10.1017/S0956796814000264>

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::SealExtent;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::Component;
use super::Container;
use super::DeclarationSlot;
use super::Half;
use super::Operand;
use super::Role;
use super::SlotIndex;
use super::StructureIndex;
use super::TypeComponent;
use super::WrittenAttribute;
use super::component_kind;
use super::declaration_half;
use super::misplaced_in;
use super::one_in;
use super::slot_refusal;
use crate::error::AscriptionForm;
use crate::error::LoweringRefusal;
use crate::error::TelescopeFault;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::shape_of;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

quenchant_shape::reason_enum! {
    /// Why an abstract component has no representation.
    pub mod representation {
        /// The reason no body member stands behind the component.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The module has not been matched yet, or its body declares no
            /// type member of the component's name.
            Unmatched,
        }
    }
}

/// Whether a module is ascribed opaquely, `:>`, and seals what it hides.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Sealed(pub bool);

/// What a reference to a stated type reads.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A manifest meaning names the written type a reference adopts; a
///   sealed one names no type, because the reference reads the atom its
///   component's abstract slot declares.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a manifest component and a transparently ascribed
///   abstract one read their types, a sealed one its atom.
/// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
/// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeMeaning
{
    /// The type written at this node, lowered once and adopted by every
    /// reference.
    Manifest(Placed),
    /// The atom the abstract slot holding the component declares.
    Sealed,
    /// The type family member at this place of the collection's family list,
    /// expanded at each application.
    Family(super::FamilyIndex),
    /// The type a functor's body writes at `defined`, read in the application
    /// `instance`: the template's type, renamed by that application.
    Instantiated
    {
        /// The type the functor's body writes.
        defined: Placed,
        /// The application whose instance reads it.
        instance: super::InstanceIndex,
    },
}

/// The body member an abstract component reads, once matched.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Represented
{
    /// The member's type.
    pub defined: Placed,
    /// The held slot owning it, which carries its refusal.
    pub held: SlotIndex,
}

/// Whether a module signature marks an abstract component `mobile`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Mark
{
    /// Written `type T`: the atom stays at the world it was made at.
    #[default]
    Unmarked,
    /// Written `mobile type T`: the atom crosses between worlds as its
    /// representation does, which the checker confirms where it seals.
    Mobile,
}

/// What one abstract component's slot is built from.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The record names the ascribing module, the component's place in
///   its signature, the kind written for it, its name tile, the body member it
///   reads once matched, its seal's extent once the module closes and the mark
///   its signature writes; it does not certify that the coordinates are live.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — an opaque ascription's abstract slot and a transparent
///   ascription's kind witness each lower from their record.
/// - witness: `tests::modules::opaque_ascription_seals`
/// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AbstractSlot
{
    /// The module whose signature states the component.
    pub structure: StructureIndex,
    /// The component's place among the signature's components.
    pub component: ComponentPlace,
    /// The kind written for it.
    pub kind: Maybe<Placed, component_kind::Absent>,
    /// Its name's tile.
    pub named: Placed,
    /// The body member it reads.
    pub representation: Maybe<Represented, representation::Absent>,
    /// How many positions after the slot its seal reaches.
    pub extent: usize,
    /// Whether the signature marks the component `mobile`.
    pub mark: Mark,
}

impl<'source> super::Structure<'source>
{
    /// The type components the module exports: its signature's under an
    /// ascription, its body's type members otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an ascribed module's signature type components, in signature
    ///   order; an unascribed module's type members, in source order.
    /// - provides: the one reading of what `M.T` can name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unascribed module's member and an ascribed
    ///   module's component are each named through the namespace.
    /// - witness: `tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    #[spec(
        ensures: |ret| ret == match self.ascription {
            | Maybe::Present(_) => self.types.as_slice(),
            | Maybe::Absent(_) => self.type_members.as_slice(),
        },
    )]
    #[inline]
    #[must_use]
    pub fn exported_types(&self) -> &[TypeComponent<'source>]
    {
        match self.ascription {
            Maybe::Present(_) => &self.types,
            Maybe::Absent(_) => &self.type_members,
        }
    }
}

/// The abstract type one sealed component declares, as it lowered.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The kind and representation are type ids of the producing core
///   arena; the extent counts the positions after the declaration its seal
///   reaches; the sealing and component numbers name the site, never a name.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a sealed counter's one abstract type carries its kind,
///   its representation, the extent through the module's last position and its
///   site.
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Sealing
{
    /// The universe the atom inhabits.
    pub kind: ValueTypeId,
    /// The type the atom stands for inside its seal.
    pub representation: ValueTypeId,
    /// How many declarations after this one read the atom as its
    /// representation.
    pub extent: SealExtent,
    /// The opaque ascription that sealed it: its module's place in the
    /// pre-order of modules.
    pub sealing: StructureIndex,
    /// Its component's place among the signature's components.
    pub component: ComponentPlace,
    /// Whether the signature marks the component `mobile`: a marked atom
    /// crosses between worlds as its representation does.
    pub mark: Mark,
}

/// One abstract type component of an opaquely ascribed module, with the
/// position of the abstract type it declares.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SealedComponent<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The admission position of its abstract type: its atom.
    pub atom: ConstantIndex,
}

/// A component's place among its signature's components, counted from the
/// first.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentPlace(pub usize);

impl From<ComponentPlace> for usize
{
    /// The place as a count of the components before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: ComponentPlace) -> Self
    {
        place.0
    }
}

/// What a kind a type component states declares.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum KindForm
{
    /// A universe, or any form other than an arrow: an abstract type.
    Universe,
    /// A value function space `(a : A, …) => U`: a type family.
    Family,
    /// A static arrow `A -> … -> U`: the kind of a type operator, formed at
    /// its classifier. A transparent ascription reads it against a family
    /// member of the spine's arity; an opaque one declares an abstract type
    /// at it, which the checker refuses unless the kind is a universe.
    Arrow,
}

impl<'source> Collector<'_, 'source>
{
    /// What `kind`, the kind a type component states, declares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: read through the parentheses written around the kind as a
    ///   whole, a family for a value function space, an arrow for a function
    ///   type, and a universe for any other form or a missing node.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold, and the
    ///   hole's refusal for parentheses that do not hold one operand.
    /// - panics: none.
    /// - executable: none — the classification is of the kind read through its
    ///   parentheses, which the postcondition could only restate by walking the
    ///   kind's pieces again.
    ///
    /// # Errors
    /// [`LoweringRefusal`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a telescope kind, an arrow kind and a universe kind
    ///   separate a family, an operator's kind and an abstract type, and an
    ///   arrow kind in parentheses is an operator's kind (#611).
    /// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
    /// - witness: `tests::modules::an_abstract_component_kinds_at_a_universe`
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `tests::modules::a_kind_reads_through_its_grouping_parentheses`
    pub(super) fn kind_form(
        &self,
        kind: Placed,
    ) -> Result<KindForm, LoweringRefusal<'source>>
    {
        let kind = super::model::ungrouped(self.pbg, self.tree, kind)?;
        let Some(node) = self.tree.node(kind.node)
        else {
            return Ok(KindForm::Universe);
        };

        Ok(match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::ValueFunctionType,
                ..
            } => KindForm::Family,
            Shape::Form {
                former: Former::ArrowType,
                ..
            } => KindForm::Arrow,
            Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                KindForm::Universe
            },
        })
    }

    /// Declare one abstract type for each abstract component of the opaquely
    /// ascribed module at `structure`, before any of its members.
    ///
    /// # Specification
    /// - requires: `structure` was just opened, so no member of it has a slot.
    /// - ensures: a sealed module takes one [`Role::Abstract`] slot per
    ///   abstract component, in signature order, each under the component's
    ///   name in the module, introduced by its name tile, owning its written
    ///   kind and recorded with the module and the component's place; a
    ///   transparent or unascribed module takes none.
    /// - provides: the atoms' admission before the members.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed module with one abstract component among
    ///   value components takes exactly one abstract slot, ahead of its
    ///   members.
    /// - witness: `tests::modules::opaque_ascription_seals`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.abstracts.len()),
        ensures: |_| {
            self.collected.slots.len().saturating_sub(before.0)
                == self.collected.abstracts.len().saturating_sub(before.1)
                && self.collected.slots.get(before.0 ..).is_some_and(|appended| {
                    appended.iter().enumerate().all(|(offset, slot)| {
                        slot.role == Role::Abstract
                            && slot.container == Container::Module(structure)
                            && self
                                .collected
                                .abstracts
                                .get(&SlotIndex(before.0.saturating_add(offset)))
                                .is_some_and(|recorded| recorded.structure == structure)
                    })
                })
        },
    )]
    pub(super) fn declare_abstracts(
        &mut self,
        structure: StructureIndex,
    )
    {
        let Some(entry) = self.collected.structures.get(structure.0)
        else {
            return;
        };
        let Maybe::Present(ref components) = entry.ascription
        else {
            return;
        };
        if !entry.sealed.0 {
            return;
        }
        let abstracts: Vec<(usize, Component<'source>)> = components
            .iter()
            .copied()
            .enumerate()
            .filter(|&(_, component)| matches!(component.form, super::ComponentForm::Abstract(_)))
            .collect();
        for (ordinal, component) in abstracts {
            let super::ComponentForm::Abstract(kind) = component.form
            else {
                continue;
            };
            let minted = SlotIndex(self.collected.slots.len());
            self.collected.slots.push(DeclarationSlot {
                name: component.name,
                container: Container::Module(structure),
                role: Role::Abstract,
                constant: ConstantIndex::from(minted.0),
                introduced_by: component.named,
                named: component.named,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Absent(declaration_half::Absent::Unwritten),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            });
            if let Maybe::Present(written) = kind {
                self.collected.own(written.node, minted);
            }
            let _fresh = self.collected.abstracts.insert(minted, AbstractSlot {
                structure,
                component: ComponentPlace(ordinal),
                kind,
                named: component.named,
                representation: Maybe::Absent(representation::Absent::Unmatched),
                extent: 0_usize,
                mark: component.mark,
            });
        }
    }

    /// Read the type member `member`, `type T = τ ;` or the family `type T(a :
    /// A, …) = τ ;`, written in `container` — a module's body or a source's
    /// top level — after the attribute blocks written before it.
    ///
    /// The attributes are kept on the member's held slot, decorating the
    /// member's form: the member declares nothing, so they state the verdict
    /// of the check a signature component reads the member through — a
    /// component's witness carries the member's form as its expectation half.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of `member`, a form in `container`
    ///   whose first tile past its attribute blocks is `type`.
    /// - ensures: a member reading `type T = τ ;` is filed among the
    ///   container's type members — the module's, or the source's top-level
    ///   ones — with a fresh held slot owning `τ` and carrying the member's
    ///   attributes; one binding parameters is filed as a family, its slot
    ///   owning the parameters' types too; a second member of an earlier one's
    ///   name in the same container is refused naming the first.
    /// - provides: the type-member half of [`Self::member`] and of a source's
    ///   top level.
    /// - fails: a member out of shape, or with an attribute block out of shape,
    ///   is refused at the member; a module's caller files it under the
    ///   module's name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] naming the module form, and an
    /// attribute block's own refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read member, a repeated one and a repaired one take
    ///   their distinct outcomes, and an attributed one keeps its attributes; a
    ///   member at a source's top level is filed under the source.
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_repeated_type_member_is_refused_naming_the_first`
    /// - witness: `tests::modules::an_unread_member_keeps_its_own_report`
    /// - witness: `tests::modules::a_component_check_carries_its_members_expectation`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.top_types.len()),
        ensures: |_| {
            self.collected.slots.len() <= before.0.saturating_add(1)
                && self.collected.top_types.len() <= before.1.saturating_add(1)
        },
    )]
    pub(super) fn type_member(
        &mut self,
        container: Container,
        member: Placed,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(FormName::MODULE));
        }
        let keyword = pieces
            .pieces
            .iter()
            .position(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::TYPE),
            )
            .unwrap_or(0_usize);
        let (blocks, form) = pieces
            .pieces
            .split_at_checked(keyword)
            .unwrap_or((&[], &pieces.pieces));
        let mut attributes = Vec::new();
        self.read_attributes(
            Cursor::new(blocks, member.span),
            member.node,
            &mut attributes,
        )?;
        let mut cursor = Cursor::new(form, member.span);
        let _keyword = cursor.tile(TileName::TYPE);
        let Maybe::Present(named) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        };
        let parameters = Self::family_parameters(&mut cursor)?;
        if let Maybe::Absent(_) = cursor.tile(TileName::EQUALS) {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        }
        let defined = one_in(FormName::MODULE, cursor.operands())?;
        let _semicolon = cursor.tile(TileName::SEMICOLON);
        if let Maybe::Present(_) = cursor.peek() {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        }
        let name = self.name_of(named);
        let first = self
            .collected
            .type_members_in(container)
            .find(|earlier| earlier.name == name)
            .and_then(|earlier| self.collected.slots.get(earlier.held.0))
            .map(|earlier| earlier.named.span);
        if let Some(first) = first {
            let refusal = LoweringRefusal::DuplicateDefinition {
                span: named.span,
                name,
                first,
            };
            let _held = self.refuse_held(container, name, member, named, refusal);
            return Ok(());
        }
        let held = self.held(container, name, member, named);
        if let Some(slot) = self.collected.slots.get_mut(held.0) {
            slot.attributes = attributes;
        }
        self.collected.own(defined.node, held);
        for parameter in &parameters {
            self.collected.own(parameter.classifier.node, held);
        }
        let meaning = if parameters.is_empty() {
            super::TypeMeaning::Manifest(defined)
        }
        else {
            let family = super::FamilyIndex(self.collected.families.len());
            self.collected.families.push(super::FamilyMember {
                held,
                parameters,
                defined,
            });
            super::TypeMeaning::Family(family)
        };
        let filed = TypeComponent {
            name,
            meaning,
            held,
        };
        match container {
            Container::Module(structure) => {
                if let Some(entry) = self.collected.structures.get_mut(structure.0) {
                    entry.type_members.push(filed);
                }
            },
            Container::TopLevel(source) => self.collected.top_types.push((source, filed)),
        }

        Ok(())
    }

    /// Match the abstract component `component`, at place `ordinal` in the
    /// signature of the module at `structure`, against the body's type member
    /// of its name.
    ///
    /// # Specification
    /// - requires: `structure`'s body is read, and `component` is abstract with
    ///   the written kind `kind`.
    /// - ensures: under an opaque ascription the component's abstract slot
    ///   records the member as its representation, takes the member's
    ///   expectation and attributes, owning their payloads, and the component
    ///   reads as its atom; under a transparent one the component reads as the
    ///   member's type, and a witness slot owning the kind checks that type at
    ///   it, unless the component is a sort a model derives, which states no
    ///   kind to check. A component no member supplies, or a family member
    ///   supplies, files its refusal on the abstract slot, so a later component
    ///   and a client reading it inherit the refusal, or on a held slot under a
    ///   transparent ascription. An opaque ascription's component at a static
    ///   arrow refuses its abstract slot as a kinded form whatever the member:
    ///   an abstract operator is an atom at a kind no universe is, which the
    ///   kernel does not admit.
    /// - provides: the abstract-component half of [`Self::match_signature`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed component, a strengthened one, a component
    ///   no member supplies, a sealed operator and a sealed component whose
    ///   member states an identity, each asserted as the exact slot and
    ///   reading.
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
    /// - witness: `tests::modules::an_abstract_component_with_no_type_member_is_refused_by_name`
    /// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
    /// - witness: `tests::modules::a_sealed_atom_reads_the_identity_its_type_member_states`
    #[spec(
        captures: before = types.len(),
        ensures: |_| types.len() <= before.saturating_add(1),
    )]
    pub(super) fn abstract_component(
        &mut self,
        structure: StructureIndex,
        ordinal: ComponentPlace,
        component: Component<'source>,
        kind: Maybe<Placed, component_kind::Absent>,
        types: &mut Vec<TypeComponent<'source>>,
    )
    {
        let container = Container::Module(structure);
        let Some(entry) = self.collected.structures.get(structure.0)
        else {
            return;
        };
        let (module, sealed) = (entry.name, entry.sealed);
        let member = entry
            .type_members
            .iter()
            .find(|member| member.name == component.name)
            .copied();
        let represented = member.and_then(|member| match member.meaning {
            super::TypeMeaning::Manifest(defined) => Some(Represented {
                defined,
                held: member.held,
            }),
            super::TypeMeaning::Sealed
            | super::TypeMeaning::Family(_)
            | super::TypeMeaning::Instantiated { .. } => None,
        });
        let unmatched = match member {
            Some(TypeComponent {
                meaning: super::TypeMeaning::Family(family),
                held,
                ..
            }) => LoweringRefusal::FamilyTelescope {
                span: self
                    .collected
                    .slots
                    .get(held.0)
                    .map_or(component.named.span, |slot| slot.named.span),
                name: component.name,
                fault: TelescopeFault::Arity {
                    stated: OperandCount::from(0_usize),
                    written: OperandCount::from(
                        self.collected
                            .families
                            .get(family.0)
                            .map_or(0_usize, |found| found.parameters.len()),
                    ),
                },
            },
            Some(_) | None => LoweringRefusal::UnknownMember {
                span: component.named.span,
                module,
                member: component.name,
            },
        };
        if sealed.0 {
            let Some(atom) = self
                .collected
                .abstracts
                .iter()
                .find(|&(_, recorded)| {
                    recorded.structure == structure && recorded.component == ordinal
                })
                .map(|(&atom, _)| atom)
            else {
                return;
            };
            let operator = matches!(kind, Maybe::Present(written) if matches!(self.kind_form(written), Ok(KindForm::Arrow)));
            match represented {
                Some(represented) if !operator => {
                    // The atom reads its member's attributes, as a
                    // transparent component's witness does: an `identity`
                    // among them states the interface the atom is admitted
                    // with, and an expectation the atom's verdict. Its
                    // payloads resolve from the atom, which owns them.
                    let (expectation, attributes) = self.member_expectation(represented.held);
                    for written in &attributes {
                        if let super::Payload::Written(payload) = written.payload {
                            self.collected.own(payload.node, atom);
                        }
                    }
                    if let Some(slot) = self.collected.slots.get_mut(atom.0) {
                        slot.signature = expectation;
                        slot.attributes = attributes;
                    }
                    if let Some(recorded) = self.collected.abstracts.get_mut(&atom) {
                        recorded.representation = Maybe::Present(represented);
                    }
                },
                Some(_) | None => {
                    let refusal = if operator {
                        LoweringRefusal::UnreadAscription {
                            span: component.named.span,
                            name: component.name,
                            form: AscriptionForm::Kinded,
                        }
                    }
                    else {
                        unmatched
                    };
                    if let Some(slot) = self.collected.slots.get_mut(atom.0) {
                        slot.refuse(component.named.node, refusal);
                    }
                },
            }
            types.push(TypeComponent {
                name: component.name,
                meaning: super::TypeMeaning::Sealed,
                held: atom,
            });
            return;
        }
        let Some(represented) = represented
        else {
            let _held = self.refuse_held(
                container,
                component.name,
                component.named,
                component.named,
                unmatched,
            );
            return;
        };
        types.push(TypeComponent {
            name: component.name,
            meaning: super::TypeMeaning::Manifest(represented.defined),
            held: represented.held,
        });
        if kind == Maybe::Absent(component_kind::Absent::Derived) {
            return;
        }
        let (expectation, attributes) = self.member_expectation(represented.held);
        let witness = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name: component.name,
            container,
            role: Role::Witness,
            constant: ConstantIndex::from(witness.0),
            introduced_by: component.named,
            named: component.named,
            signature: expectation,
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes,
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });
        if let Maybe::Present(written) = kind {
            self.collected.own(written.node, witness);
        }
        let _fresh = self.collected.abstracts.insert(witness, AbstractSlot {
            structure,
            component: ordinal,
            kind,
            named: component.named,
            representation: Maybe::Present(represented),
            extent: 0_usize,
            mark: component.mark,
        });
    }

    /// Fix the extent of every seal the module at `structure` declared, once
    /// its body, its signature and every layer under it are matched.
    ///
    /// # Specification
    /// - requires: `structure` is closing: every slot it will take is taken.
    /// - ensures: each abstract slot the module declared reaches every position
    ///   after it through the last slot taken so far; no other record changes.
    /// - provides: the reach of each seal, which ends with its module.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed counter's seal reaches its members and the
    ///   witnesses its signature filed, and a declaration after the module
    ///   reads the atom outside.
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_later_seal_leaves_an_earlier_extent`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every abstract slot once to fix the module's extents; the check reads each once more"
        )
    )]
    #[spec(
        captures: last = self.collected.slots.len().saturating_sub(1),
        ensures: |_| self.collected.abstracts.iter().all(|(&slot, recorded)| {
            recorded.structure != structure
                || !matches!(self.collected.slots.get(slot.0), Some(declared) if declared.role == Role::Abstract)
                || recorded.extent == last.saturating_sub(slot.0)
        }),
    )]
    pub(super) fn seal(
        &mut self,
        structure: StructureIndex,
    )
    {
        let last = self.collected.slots.len().saturating_sub(1_usize);
        for (&slot, recorded) in &mut self.collected.abstracts {
            if recorded.structure == structure
                && self
                    .collected
                    .slots
                    .get(slot.0)
                    .is_some_and(|declared| declared.role == Role::Abstract)
            {
                recorded.extent = last.saturating_sub(slot.0);
            }
        }
    }

    /// Whether the type member forms of a module body include `pieces`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: affirmative exactly when the reading's first tile outside its
    ///   leading attribute blocks, `@[ … ]`, is `type`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type member and a definition member are told apart
    ///   by their first tile, an attribute block before either kept apart.
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_component_check_carries_its_members_expectation`
    #[spec(
        ensures: |ret| !ret.0 || pieces.pieces.iter().any(|piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::TYPE)),
    )]
    pub(super) fn opens_type_member(pieces: &Pieces) -> TypeMemberForm
    {
        let mut block = false;
        for piece in &pieces.pieces {
            match *piece {
                Piece::Tile { label, .. } if block => block = label != TileName::BRACKET_CLOSE,
                Piece::Operand(_) if block => {},
                Piece::Tile { label, .. } if label == TileName::ATTRIBUTES => block = true,
                Piece::Tile { label, .. } => return TypeMemberForm(label == TileName::TYPE),
                Piece::Operand(_) => return TypeMemberForm(false),
            }
        }

        TypeMemberForm(false)
    }

    /// The expectation a component's check reads off the type member at
    /// `held`: the member's form as the check's half, under which the
    /// member's attributes are filed, and those attributes, taken off the
    /// member.
    ///
    /// A member declares nothing, and the witness that checks the member's
    /// code at the component's kind is filed by no form of its own, so without
    /// this half the verdict of the check has no attribute to state it. The
    /// alternative, an expectation written on the module, would state every
    /// component's check at once; the component's own form sits in the
    /// signature, where no declaration is written to carry attributes. The
    /// half lowers to nothing: the witness's outcome is its check's.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the member's form as a [`Operand::Signature`] half and the
    ///   member's attributes, taken out of the member, when `held` names a
    ///   slot; nothing otherwise.
    /// - provides: the expectation of the witness [`Self::abstract_component`]
    ///   and [`Self::family_component`] file, and of the atom a sealed abstract
    ///   component files.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a transparent component's witness and a family
    ///   component's witness each read the expectation on their member.
    /// - witness: `tests::modules::a_component_check_carries_its_members_expectation`
    #[spec(
        captures: before = self.collected.slots.get(held.0).map(|member| (member.introduced_by, member.named, member.attributes.clone())),
        ensures: |ret| match before {
            | Some((form, named, ref attributes)) => ret.0 == Maybe::Present(Half { declaration: form, named, operand: Operand::Signature })
                && ret.1 == *attributes
                && self.collected.slots.get(held.0).is_some_and(|member| member.attributes.is_empty()),
            | None => matches!(ret.0, Maybe::Absent(_)) && ret.1.is_empty(),
        },
    )]
    pub(super) fn member_expectation(
        &mut self,
        held: SlotIndex,
    ) -> (
        Maybe<Half, declaration_half::Absent>,
        Vec<WrittenAttribute<'source>>,
    )
    {
        match self.collected.slots.get_mut(held.0) {
            Some(member) => (
                Maybe::Present(Half {
                    declaration: member.introduced_by,
                    named: member.named,
                    operand: Operand::Signature,
                }),
                core::mem::take(&mut member.attributes),
            ),
            None => (
                Maybe::Absent(declaration_half::Absent::Unwritten),
                Vec::new(),
            ),
        }
    }

    /// Refuse every attribute a type member still holds once every module is
    /// matched: no component's check read it, so it states nothing.
    ///
    /// # Specification
    /// - requires: every module is closed.
    /// - ensures: each type member left holding attributes holds none, and its
    ///   module is refused with a misplaced tile at the first of them, as an
    ///   attribute block before a form that declares nothing is.
    /// - provides: the refusal of an expectation with no verdict to state.
    /// - fails: never; a fault is filed rather than raised.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an attributed member with no component reading it
    ///   refuses its module, and one a component reads does not.
    /// - witness: `tests::modules::a_component_check_carries_its_members_expectation`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every structure's type members once; the check reads each once more"
        )
    )]
    #[spec(
        ensures: |_| self.collected.structures.iter().flat_map(|entry| entry.type_members.iter()).all(|member| {
            self.collected.slots.get(member.held.0).is_none_or(|slot| slot.attributes.is_empty())
        }),
    )]
    pub(super) fn stray_expectations(&mut self)
    {
        let members: Vec<(StructureIndex, SlotIndex)> = self
            .collected
            .structures
            .iter()
            .enumerate()
            .flat_map(|(index, entry)| {
                entry
                    .type_members
                    .iter()
                    .map(move |member| (StructureIndex(index), member.held))
            })
            .collect();
        for (structure, held) in members {
            let Some(member) = self.collected.slots.get_mut(held.0)
            else {
                continue;
            };
            let Some(first) = member.attributes.first().map(|written| written.span)
            else {
                continue;
            };
            member.attributes.clear();
            let form = member.introduced_by;
            self.fault_at(structure, form, misplaced_in(FormName::MODULE, first));
        }
    }
}

/// Whether a module member form is a type member.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct TypeMemberForm(pub bool);
