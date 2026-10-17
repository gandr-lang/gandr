//! Type families and the components a model signature derives, as the
//! collection pass reads them. The derivation itself lives with the model
//! signature (`crate::model`); the minting half with the lowering
//! (`crate::lower::model`).
//!
//! # A family is a type member over parameters
//!
//! A module body declares a type family as a type member binding
//! parameters, `type Hom(a : Ob, b : Ob) = τ ;`, and every parameter is in
//! scope in `τ`. A reference `Hom(x, y)` stands for `τ` with the arguments
//! substituted for the parameters: the family is transparent, expanded where
//! it is named, so a model's family is definitionally the type its body
//! writes. A signature states a family component as `type Hom : (a : Ob, b :
//! Ob) => Type`, its index telescope written as a telescope Π into a
//! universe; the component's meaning is the body's family member of its
//! name, and the member's parameters must take the indices the component
//! states — as many, each at the type its index states.
//!
//! - Choice: expansion of the member's type. Alternatives: a static operator
//!   `Hom : Ob -> Ob -> Type` decoded at each use, which confines the indices
//!   to the static classifiers a code can quote; a nominal family, which no
//!   model could define by a type it already has. Reversal: a family sealed by
//!   `:>`, which needs a family atom the core does not declare yet, so a sealed
//!   family component stays [`AscriptionForm::Kinded`].
//!
//! # `Model(S)` is the signature the sign `S` derives
//!
//! A module ascribed `: Model(S)` is matched against the components the sign
//! `S`, declared before it, derives (`crate::model::derive`): each unindexed
//! sort an abstract component, each indexed sort a family component, each
//! operation and each law a value component whose type is minted from the
//! derivation rather than read from a written form. A component the
//! derivation cannot state is refused under its name with the derivation's
//! reason; a component its module does not define is refused as a written
//! one is. `S` is a reference to the declaration `S : Sig` the block defines,
//! and the derivation reads that declaration's value: `Model` is a function
//! from `Sig` the elaborator applies, not a second reading of the block.
//!
//! - Choice: `S` resolves by name to the definition the block declared before
//!   the module, and `Model` runs at elaboration. Alternatives: a core function
//!   `Model : Sig -> Type`, which needs a record of types computed from a value
//!   the kernel does not state; a module-level import of the sign's derived
//!   components. Reversal: a `Sig` value the elaborator cannot read off a
//!   definition — a parameter, or a computed presentation — whose model the
//!   core would then compute from the normal form.
//!
//! A derived sort states no kind (`component_kind::Absent::Derived`): its
//! size is the model's, so `type Ob = Type` is a model whatever universe the
//! written signature `type Ob : Type[+, 1]` would demand.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::Component;
use super::ComponentForm;
use super::ComponentPlace;
use super::ComponentScope;
use super::Container;
use super::DeclarationSlot;
use super::Half;
use super::Member;
use super::Operand;
use super::Role;
use super::SlotIndex;
use super::StructureIndex;
use super::TypeComponent;
use super::TypeMeaning;
use super::component_kind;
use super::declaration_half;
use super::declared_member;
use super::misplaced_in;
use super::one_in;
use super::slot_refusal;
use crate::error::AscriptionForm;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
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
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::model::ModelForm;
use crate::model::ModelSignature;
use crate::resolve::HeadArity;
use crate::resolve::OperandCount;

quenchant_shape::reason_enum! {
    /// Why a module carries no derived model signature.
    pub mod derived {
        /// The reason no derivation stands behind the module's ascription.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The module is unascribed, or its signature is written out.
            Written,
        }
    }
}

/// A derived model signature's place in the collection's model list.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ModelIndex(pub usize);

impl From<ModelIndex> for usize
{
    /// The place as a count of the models before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ModelIndex) -> Self
    {
        index.0
    }
}

/// A type family member's place in the collection's family list.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FamilyIndex(pub usize);

impl From<FamilyIndex> for usize
{
    /// The place as a count of the families before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: FamilyIndex) -> Self
    {
        index.0
    }
}

/// A parameterized component's place in the collection's parameter lists.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterList(pub usize);

impl From<ParameterList> for usize
{
    /// The place as a count of the lists before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ParameterList) -> Self
    {
        index.0
    }
}

/// One component of a derived model signature: the model and the
/// component's place in it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ModelPart
{
    /// The model signature.
    pub model: ModelIndex,
    /// The component's place among its components.
    pub component: ComponentPlace,
}

/// How a family component states its index telescope.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FamilyForm
{
    /// The kind written for it: a telescope Π into a universe, `(a : A, …)
    /// => U`, or an arrow spine into one, `A -> … -> U`, which states its
    /// indices without binding them.
    Written(Placed),
    /// The indices its module's model signature derives at the component's
    /// place.
    Derived,
}

/// One parameter of a type family member: its name's tile and its type.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FamilyParameter
{
    /// The parameter's name.
    pub named: Placed,
    /// The type it was written with.
    pub classifier: Placed,
}

/// A type family member, `type F(a : A, …) = τ ;`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the parameters keep source order, each typed under the ones
///   before it, and `τ` names every one of them; the held slot owns the
///   parameters' types and `τ` and carries their refusal.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a two-parameter family expands at each reference to its
///   type over the arguments.
/// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FamilyMember
{
    /// The held slot owning the member's types.
    pub held: SlotIndex,
    /// The parameters, in source order.
    pub parameters: Vec<FamilyParameter>,
    /// The type the family stands for.
    pub defined: Placed,
}

/// What one family component's check slot compares: the member's parameters
/// against the index telescope the component states.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct FamilyCheck
{
    /// The module whose signature states the component.
    pub structure: StructureIndex,
    /// The component's place among its signature's components.
    pub component: ComponentPlace,
    /// The body's family member.
    pub family: FamilyIndex,
    /// How the component states its indices.
    pub stated: FamilyForm,
}

impl<'source> Collector<'_, 'source>
{
    /// File the manifest family component `component`, `type F(a : A, …) =
    /// τ`, of the module `container`, whose parameters are the list at
    /// `parameters`.
    ///
    /// # Specification
    /// - requires: `parameters` is a list [`Self::signature`] filed, matched
    ///   once.
    /// - ensures: a held slot under the component's name owns each parameter's
    ///   type and `τ`, each read under the components before it; the family is
    ///   filed with its parameters and pushed onto `types` as the component's
    ///   meaning, so a later component or a client applying it expands it over
    ///   its arguments.
    /// - provides: the manifest-family half of [`Self::match_signature`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-parameter manifest family beside a value
    ///   component lowers, and one applied to no arguments is refused.
    /// - witness: `modules::modules::a_manifest_family_component_binds_two_parameters`
    /// - witness: `modules::modules::a_type_component_arity_mismatch_is_refused_by_name`
    #[spec(
        captures: before = (types.len(), self.collected.families.len()),
        ensures: types.len() == before.0.saturating_add(1)
            && self.collected.families.len() == before.1.saturating_add(1),
    )]
    pub(super) fn manifest_family(
        &mut self,
        container: Container,
        component: Component<'source>,
        parameters: ParameterList,
        defined: Placed,
        scope: ComponentScope,
        types: &mut Vec<TypeComponent<'source>>,
    )
    {
        let held = self.held(container, component.name, component.named, component.named);
        let parameters = self
            .collected
            .parameter_lists
            .get_mut(parameters.0)
            .map(core::mem::take)
            .unwrap_or_default();
        self.collected.own(defined.node, held);
        self.collected.scopes.push((defined.node, scope));
        for parameter in &parameters {
            self.collected.own(parameter.classifier.node, held);
            self.collected
                .scopes
                .push((parameter.classifier.node, scope));
        }
        let family = FamilyIndex(self.collected.families.len());
        self.collected.families.push(FamilyMember {
            held,
            parameters,
            defined,
        });
        types.push(TypeComponent {
            name: component.name,
            meaning: TypeMeaning::Family(family),
            held,
        });
    }

    /// Read a model signature, `Model(S)`, after its `:` or `:>`.
    ///
    /// # Specification
    /// - requires: `cursor` stands on the former's name, just past the
    ///   ascription's `:` or `:>` of the module form `form`.
    /// - ensures: the cursor past `)`; the signature derived from the value of
    ///   the declaration `S` a `sign` block defined wholly before `form`, and
    ///   one component per derived component in its order, each named by its
    ///   member's name at the ascription's `S` tile: an unindexed sort an
    ///   abstract component of no kind, an indexed sort a derived family, and
    ///   every other component — one the derivation cannot state among them — a
    ///   derived value.
    /// - provides: the model half of [`Self::header`].
    /// - fails: a misplaced tile for a former out of shape; an unresolved head
    ///   for a former other than `Model`, or for an `S` that names no
    ///   declaration a `sign` block defined before the module; an unadmitted
    ///   form for a value that codes no presentation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`],
    /// [`LoweringRefusal::UnresolvedTypeHead`] and
    /// [`LoweringRefusal::OutOfFragment`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CatShape` model and a former naming an
    ///   undeclared sign, each asserted as the exact components or refusal.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_model_of_an_undeclared_sign_is_refused_by_name`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body names every derived component once; the check compares each name once"
        )
    )]
    #[spec(
        ensures: |ret| ret.as_ref().map_or(true, |found| {
            found.0.len() == found.1.components.len()
                && found.0.iter().zip(&found.1.components).all(|(component, derived)| {
                    component.name == self.name_of(derived.named)
                        && match derived.form {
                            | Ok(ModelForm::Sort { ref indices }) if indices.is_empty() => {
                                component.form == ComponentForm::Abstract(Maybe::Absent(component_kind::Absent::Derived))
                            },
                            | Ok(ModelForm::Sort { .. }) => {
                                component.form == ComponentForm::Family(FamilyForm::Derived)
                            },
                            | Ok(ModelForm::Operation { .. } | ModelForm::Law { .. }) | Err(_) => {
                                component.form == ComponentForm::Derived
                            },
                        }
                })
        }),
    )]
    pub(super) fn model_signature(
        &self,
        cursor: &mut Cursor<'_>,
        form: Placed,
    ) -> Result<(Vec<Component<'source>>, ModelSignature), LoweringRefusal<'source>>
    {
        let Maybe::Present(former) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        }
        let Maybe::Present(sign) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        }
        let named = self.name_of(former);
        if named.as_ref() != "Model" {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: former.span,
                name: named,
                arity: HeadArity::Unary,
            });
        }
        let name = self.name_of(sign);
        let presented = self
            .collected
            .by_name
            .get(&(self.collected.top(form.span.start()), name))
            .and_then(|&position| self.collected.slots.get(position.0))
            .filter(|slot| {
                slot.introduced_by.span.end() <= form.span.start()
                    && matches!(
                        slot.definition,
                        Maybe::Present(Half {
                            operand: Operand::Presented,
                            ..
                        })
                    )
            })
            .and_then(|slot| self.collected.descriptions.get(&slot.introduced_by.node))
            .and_then(|entry| match entry.presentation {
                Maybe::Present(ref presentation) => Some(presentation),
                Maybe::Absent(_) => None,
            });
        let Some(presentation) = presented
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: sign.span,
                name,
                arity: HeadArity::Nullary,
            });
        };
        let Ok(model) = crate::model::derive(presentation)
        else {
            return Err(LoweringRefusal::OutOfFragment {
                span: sign.span,
                form: FormName::MODULE,
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::Unadmitted,
            });
        };
        let components = model
            .components
            .iter()
            .map(|derived| Component {
                name: self.name_of(derived.named),
                named: sign,
                form: match derived.form {
                    Ok(ModelForm::Sort { ref indices }) if indices.is_empty() => {
                        ComponentForm::Abstract(Maybe::Absent(component_kind::Absent::Derived))
                    },
                    Ok(ModelForm::Sort { .. }) => ComponentForm::Family(FamilyForm::Derived),
                    Ok(ModelForm::Operation { .. } | ModelForm::Law { .. }) | Err(_) => {
                        ComponentForm::Derived
                    },
                },
            })
            .collect();

        Ok((components, model))
    }

    /// Read a type member's parameters, `( a : A, … )`, the cursor standing
    /// just past the member's name.
    ///
    /// # Specification
    /// - requires: `cursor` stands past the name tile of a type member.
    /// - ensures: no parameters when no `(` follows; otherwise every parameter
    ///   in order, each a name and one type, the cursor past `)`.
    /// - fails: a misplaced tile or a missing or extra operand.
    /// - panics: none.
    /// - executable: none — the parameters are the cursor's pieces, which a
    ///   postcondition cannot re-read once the cursor has moved past them.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-parameter family is read whole, and one whose
    ///   parameter has no type is refused.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_family_of_the_wrong_telescope_is_refused`
    pub(super) fn family_parameters(
        cursor: &mut Cursor<'_>
    ) -> Result<Vec<FamilyParameter>, LoweringRefusal<'source>>
    {
        let mut parameters = Vec::new();
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
            return Ok(parameters);
        }
        loop {
            let named = match cursor.peek() {
                Maybe::Present(Piece::Tile { label, at })
                    if label == TileName::TYPE_VARIABLE || label == TileName::IDENTIFIER =>
                {
                    let _named = cursor.tile(label);
                    at
                },
                Maybe::Present(_) | Maybe::Absent(_) => {
                    return Err(misplaced_in(FormName::PARAMETER, cursor.here()));
                },
            };
            if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                return Err(misplaced_in(FormName::PARAMETER, cursor.here()));
            }
            let classifier = one_in(FormName::PARAMETER, cursor.operands())?;
            parameters.push(FamilyParameter { named, classifier });
            if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                continue;
            }
            if let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE) {
                return Ok(parameters);
            }
            return Err(misplaced_in(FormName::PARAMETERS, cursor.here()));
        }
    }

    /// How many indices the written kind `kind`, `(a : A, …) => U` or `A -> …
    /// -> U`, states.
    ///
    /// # Specification
    /// - requires: `kind` is a value function space or a static arrow.
    /// - ensures: for a static arrow, one per arrow along its spine; otherwise
    ///   the number of entries its parenthesised domain lists, or one for a
    ///   domain written bare; none for a kind without a domain.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold, and the
    ///   spine's refusal.
    /// - panics: none.
    /// - executable: none — the count is the pieces' reading, which the
    ///   postcondition could only restate by reading them again.
    ///
    /// # Errors
    /// [`LoweringRefusal`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-index kind against a one-parameter member is
    ///   refused naming both counts, whether written as a telescope or a spine.
    /// - witness: `modules::modules::models::a_family_of_the_wrong_telescope_is_refused`
    /// - witness: `modules::modules::models::a_written_family_of_the_wrong_telescope_is_refused`
    /// - witness: `modules::modules::a_kinded_type_component_spine_declares_its_arity`
    fn kind_arity(
        &self,
        kind: Placed,
    ) -> Result<OperandCount, LoweringRefusal<'source>>
    {
        if self.kind_form(kind) == Ok(super::KindForm::Arrow) {
            return Ok(OperandCount::from(
                spine_domains(self.pbg, self.tree, kind)?.len(),
            ));
        }
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, kind.node, &mut pieces)?;
        let Some(domain) = pieces.pieces.iter().find_map(|piece| match *piece {
            Piece::Operand(operand) => Some(operand),
            Piece::Tile { .. } => None,
        })
        else {
            return Ok(OperandCount::from(0_usize));
        };
        let parenthesized = self.tree.node(domain.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::ParenthesizedType,
                    ..
                })
            )
        });
        if !parenthesized {
            return Ok(OperandCount::from(1_usize));
        }
        let mut entries = Pieces::new();
        read_pieces(self.pbg, self.tree, domain.node, &mut entries)?;
        let mut count = 0_usize;
        let mut written = false;
        for piece in &entries.pieces {
            match *piece {
                Piece::Operand(_) => written = true,
                Piece::Tile { label, .. } => {
                    if label == TileName::COMMA || label == TileName::PAREN_CLOSE {
                        count = count.saturating_add(usize::from(written));
                        written = false;
                    }
                },
            }
        }

        Ok(OperandCount::from(count))
    }

    /// Match the family component `component` of the module at `structure`
    /// against the body's family member of its name.
    ///
    /// # Specification
    /// - requires: `structure`'s body is read and `component` states a family
    ///   by `form`.
    /// - ensures: a family member binding as many parameters as the component
    ///   states indices is pushed onto `types` as the component's meaning, and
    ///   a check slot is filed comparing each parameter's type with its index's
    ///   — the witness owning a written kind, which sees the components before
    ///   it, or a held slot for a derived one. A sealed module, a member that
    ///   is no family or of another count, and a component no member supplies
    ///   each refuse a held slot under the component's name instead.
    /// - provides: the family half of [`Self::match_signature`].
    /// - fails: never; a fault is filed rather than raised.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written and a derived family each read their
    ///   member, and a member of the wrong count is refused naming both.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_family_of_the_wrong_telescope_is_refused`
    /// - witness: `modules::modules::models::a_written_family_of_the_wrong_telescope_is_refused`
    #[spec(
        captures: before = types.len(),
        ensures: |_| types.len() <= before.saturating_add(1),
    )]
    pub(super) fn family_component(
        &mut self,
        structure: StructureIndex,
        place: ComponentPlace,
        component: Component<'source>,
        form: FamilyForm,
        scope: ComponentScope,
        types: &mut Vec<TypeComponent<'source>>,
    )
    {
        let container = Container::Module(structure);
        let Some(entry) = self.collected.structures.get(structure.0)
        else {
            return;
        };
        let (module, sealed, model) = (entry.name, entry.sealed, entry.model);
        let member = entry
            .type_members
            .iter()
            .find(|member| member.name == component.name)
            .copied();
        let refuse = |collector: &mut Self, refusal| {
            let _held = collector.refuse_held(
                container,
                component.name,
                component.named,
                component.named,
                refusal,
            );
        };
        if sealed.0 {
            refuse(self, LoweringRefusal::UnreadAscription {
                span: component.named.span,
                name: component.name,
                form: AscriptionForm::Kinded,
            });
            return;
        }
        let stated = match form {
            FamilyForm::Written(kind) => match self.kind_arity(kind) {
                Ok(count) => count,
                Err(refusal) => {
                    refuse(self, refusal);
                    return;
                },
            },
            FamilyForm::Derived => self.derived_indices(model, place),
        };
        let Some(member) = member
        else {
            refuse(self, LoweringRefusal::UnknownMember {
                span: component.named.span,
                module,
                member: component.name,
            });
            return;
        };
        let family = match member.meaning {
            TypeMeaning::Family(family) => Some(family),
            TypeMeaning::Manifest(_) | TypeMeaning::Sealed | TypeMeaning::Instantiated { .. } => {
                None
            },
        };
        let written = OperandCount::from(family.map_or(0_usize, |family| {
            self.collected
                .families
                .get(family.0)
                .map_or(0_usize, |found| found.parameters.len())
        }));
        let Some(family) = family.filter(|_| written == stated)
        else {
            let span = self
                .collected
                .slots
                .get(member.held.0)
                .map_or(component.named.span, |held| held.named.span);
            refuse(self, LoweringRefusal::FamilyTelescope {
                span,
                name: component.name,
                fault: TelescopeFault::Arity { stated, written },
            });
            return;
        };
        types.push(TypeComponent {
            name: component.name,
            meaning: TypeMeaning::Family(family),
            held: member.held,
        });
        let check = match form {
            FamilyForm::Written(kind) => {
                let (expectation, attributes) = self.member_expectation(member.held);
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
                self.collected.own(kind.node, witness);
                self.collected.scopes.push((kind.node, scope));
                witness
            },
            FamilyForm::Derived => {
                self.held(container, component.name, component.named, component.named)
            },
        };
        let _fresh = self.collected.family_checks.insert(check, FamilyCheck {
            structure,
            component: place,
            family,
            stated: form,
        });
    }

    /// How many indices the sort at `place` of the model `model` binds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the length of the sort's derived index telescope; none for an
    ///   absent model, an absent place, or a component other than a sort.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CatShape` `Hom` binds two indices.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(ensures: |ret| matches!(model, Maybe::Present(_)) || ret == OperandCount::from(0_usize))]
    fn derived_indices(
        &self,
        model: Maybe<ModelIndex, derived::Absent>,
        place: ComponentPlace,
    ) -> OperandCount
    {
        let Maybe::Present(index) = model
        else {
            return OperandCount::from(0_usize);
        };
        OperandCount::from(
            self.collected
                .models
                .get(index.0)
                .and_then(|signature| signature.components.get(place.0))
                .map_or(0_usize, |component| match component.form {
                    Ok(ModelForm::Sort { ref indices }) => indices.len(),
                    Ok(ModelForm::Operation { .. } | ModelForm::Law { .. }) | Err(_) => 0_usize,
                }),
        )
    }

    /// State the derived value component `component`, at `place` in the model
    /// signature of the module at `structure`, for the member of its name.
    ///
    /// # Specification
    /// - requires: `structure`'s body is read and ascribed a model signature.
    /// - ensures: a component the derivation states is stated for the
    ///   definition member of its name as [`Self::state`] states a written
    ///   type, the member yielded; a component the derivation cannot state, a
    ///   name a nested module answers, and a name nothing answers each refuse a
    ///   held slot under the component's name, and nothing is yielded.
    /// - provides: the derived half of [`Self::match_signature`].
    /// - fails: never; a fault is filed rather than raised.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CatShape` operations and laws each type their
    ///   member, and a missing operation is refused naming it.
    /// - witness: `modules::modules::models::a_derived_signature_states_what_the_written_one_does`
    /// - witness: `modules::modules::models::a_model_missing_an_operation_is_refused_naming_it`
    #[spec(
        captures: before = self.member_named(Container::Module(structure), component.name),
        ensures: |ret| match ret {
            | Maybe::Present(found) => before == Maybe::Present(found),
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn derived_component(
        &mut self,
        structure: StructureIndex,
        component: Component<'source>,
        place: ComponentPlace,
        scope: ComponentScope,
    ) -> Maybe<Member, declared_member::Absent>
    {
        let container = Container::Module(structure);
        let undeclared = Maybe::Absent(declared_member::Absent::Undeclared);
        let Some(entry) = self.collected.structures.get(structure.0)
        else {
            return undeclared;
        };
        let module = entry.name;
        let Maybe::Present(model) = entry.model
        else {
            return undeclared;
        };
        let fault = self
            .collected
            .models
            .get(model.0)
            .and_then(|signature| signature.components.get(place.0))
            .and_then(|derived| derived.form.as_ref().err().copied());
        let refusal = match (fault, self.member_named(container, component.name)) {
            (Some(fault), _) => LoweringRefusal::UnstatedComponent {
                span: component.named.span,
                name: component.name,
                fault,
            },
            (None, Maybe::Present(Member::Slot(slot))) => {
                let part = ModelPart {
                    model,
                    component: place,
                };
                self.state(
                    slot,
                    Operand::Model(part),
                    component.named,
                    Maybe::Present(scope),
                );
                return Maybe::Present(Member::Slot(slot));
            },
            (None, Maybe::Present(Member::Module(_))) => LoweringRefusal::OutOfFragment {
                span: component.named.span,
                form: FormName::MODULE,
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
            },
            (None, Maybe::Absent(_)) => LoweringRefusal::UnknownMember {
                span: component.named.span,
                module,
                member: component.name,
            },
        };
        let _held = self.refuse_held(
            container,
            component.name,
            component.named,
            component.named,
            refusal,
        );

        undeclared
    }
}

/// The domains of the arrow spine `kind`, `A -> … -> U`, outermost first.
///
/// The spine is the codomain chain: `A -> B -> U` and `A -> (B -> U)` each
/// state two domains, and `(A -> B) -> U` states one, an operator's kind. A
/// kind that is no arrow states none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one domain per arrow walked from `kind` down its codomains,
///   through any parentheses around a codomain, outermost first.
/// - provides: the arity and the indices of a kind written as a static arrow.
/// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold, and the hole's
///   refusal for an arrow whose domain or codomain is not one operand.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal`].
///
/// # Termination
/// - reason: each step moves to a child of the node before it, not recursion.
/// - measure: the depth of the kind's subtree below the current node.
///
/// # Adequacy
/// - hypothesis: L3 — `Type -> Type -> Type` states two domains and a member
///   binding one parameter against it is refused naming both counts.
/// - witness: `modules::modules::a_kinded_type_component_spine_declares_its_arity`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |domains| domains.iter().all(|domain| domain.span.start() >= kind.span.start())))]
pub fn spine_domains<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    kind: Placed,
) -> Result<Vec<Placed>, LoweringRefusal<'source>>
{
    let mut domains = Vec::new();
    let mut position = kind;
    loop {
        let Some(node) = tree.node(position.node)
        else {
            return Ok(domains);
        };
        let former = match shape_of(pbg, node)? {
            Shape::Form { former, .. } => former,
            Shape::Root | Shape::Repair(_) | Shape::Layout => return Ok(domains),
        };
        let mut pieces = Pieces::new();
        read_pieces(pbg, tree, position.node, &mut pieces)?;
        let mut cursor = Cursor::new(&pieces.pieces, position.span);
        position = match former {
            Former::ArrowType => {
                domains.push(one_in(FormName::MODULE, cursor.operands())?);
                if let Maybe::Absent(_) = cursor.tile(TileName::ARROW) {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                }
                one_in(FormName::MODULE, cursor.operands())?
            },
            Former::ParenthesizedType if !domains.is_empty() => {
                if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                }
                one_in(FormName::MODULE, cursor.operands())?
            },
            Former::Name
            | Former::Constructor
            | Former::Hole
            | Former::Number
            | Former::Text
            | Former::Parenthesized
            | Former::Unit
            | Former::Thunk
            | Former::Lambda
            | Former::Block
            | Former::Return
            | Former::Exit
            | Former::Become
            | Former::Loop
            | Former::While
            | Former::For
            | Former::Break
            | Former::Continue
            | Former::Force
            | Former::Run
            | Former::Call
            | Former::Case
            | Former::Telescope
            | Former::Injection
            | Former::LazyRecord
            | Former::Binary
            | Former::Unary
            | Former::Projection
            | Former::TypeHead
            | Former::TypePath
            | Former::Universe
            | Former::TypeApplication
            | Former::ThunkType
            | Former::ReturnerType
            | Former::ProductType
            | Former::SumType
            | Former::LazyProductType
            | Former::TelescopeType
            | Former::LabelledSumType
            | Former::LazyRecordType
            | Former::ValueFunctionType
            | Former::StaticAbstraction
            | Former::ParenthesizedType
            | Former::PathType
            | Former::RelationType
            | Former::CapabilityType
            | Former::AtType
            | Former::Scope
            | Former::Declaration
            | Former::AttributeBlock
            | Former::Import
            | Former::Module
            | Former::Data
            | Former::Mutual
            | Former::Instantiation
            | Former::SessionType
            | Former::Action
            | Former::Offer
            | Former::Access
            | Former::Reserved
            | Former::Unadmitted => return Ok(domains),
        };
    }
}
