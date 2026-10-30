//! `Eq.generic(T)` in the lowering: a definition whose type and body are the
//! equality derived from the data declaration `T`; `Eq.generic.refl(T)` and
//! `Eq.generic.sym(T)`, the laws that equality satisfies.
//!
//! # The spelling
//!
//! The prelude declares `module Eq { def generic : (T : Type) => (T, T) =>
//! Bool ; }`, a member with a signature and no body. A definition written
//! `def eq = Eq.generic(T)`, inside a model of `Eq` or anywhere else, is
//! lowered to the ordinary declaration [`gandr_core_term::generic::equality`]
//! writes for `T`: structural equality over its constructors, the checker
//! judging it and the kernel readmitting it as it does any declaration. The
//! prelude's member itself lowers to nothing: it names the derivation and is
//! no term ([`Role::Generic`]).
//!
//! `def refl = Eq.generic.refl(T)` and `def sym = Eq.generic.sym(T)` lower
//! to the proofs [`gandr_core_term::generic::law::law`] writes, by congruence
//! over `T`'s constructors, each field's law the host's admitted one at an
//! integer or a string (the prelude's `EqInteger` and `EqString`) and the
//! derived one at another declaration. A model of `Eq` whose equality is
//! derived proves its laws so. Transitivity is not derived: its proof inverts
//! a conjunction, which waits on a case whose motive reads its scrutinee
//! (#2374), as does a law over a field of a sum or a tuple.
//!
//! # The reading
//!
//! - Each call is read only as a definition's whole body; anywhere else it is
//!   refused [`LoweringRefusal::GenericMisplaced`]. The declaration it writes
//!   is named like any other, so a use site needs no rule of its own; a use
//!   standing elsewhere waits on data codes as values (#2343).
//! - The derivation lives in core-term and is untrusted: what it does not cover
//!   it refuses by name ([`LoweringRefusal::GenericUncovered`]), and what it
//!   writes the checker judges as source.
//! - The derivation reads each declaration it reaches off its levitated code,
//!   decoded here: the constructor table, each constructor's product spine, a
//!   `var` of the family as the recursion and each leaf at the type it names. A
//!   family the description route reads only natively, as one with a function
//!   field, is refused at the first field its code cannot carry.
//! - A definition that also states its type is checked at the stated type, so a
//!   signature that disagrees with the derived equality or law is refused where
//!   it was written; a model's law is checked so at its theory's statement.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::description::DecodeContext;
use gandr_core_term::description::ParameterDepth;
use gandr_core_term::description::TypeArity;
use gandr_core_term::description::TypeBinding;
use gandr_core_term::description::decode_ref;
use gandr_core_term::generic::Uncovered;
use gandr_core_term::generic::equality;
use gandr_core_term::generic::law::Statement;
use gandr_core_term::generic::law::law;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::OccurrenceSite;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::CodeView;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::ValueTypeRef;
use gandr_theory_levitation::ValueTypeView;
use quenchant_shape::shape::Maybe;

use super::Former;
use super::Frame;
use super::Lowerer;
use super::NamePath;
use super::PathResolution;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Recognized;
use super::Resolved;
use super::Segment;
use super::Sink;
use super::Site;
use super::atom_type;
use super::exactly;
use super::identity::spelled;
use crate::description::DescriptionFault;
use crate::description::NativeFamily;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::module::DeclarationSlot;
use crate::module::Half;
use crate::module::Operand;
use crate::module::Role;
use crate::module::SlotIndex;
use crate::origin::Origin;
use crate::resolve::SurfaceName;
use crate::resolve::type_atom;

#[cfg(test)]
mod tests;

/// The prelude module that declares the derivation.
const MODULE: &str = "Eq";

/// The derivation's name in [`MODULE`].
const MEMBER: &str = "generic";

/// The laws a derived equality proves, by the member of [`MEMBER`] that names
/// each.
const LAWS: [(&str, Statement); 2] = [
    ("refl", Statement::Reflexive),
    ("sym", Statement::Symmetric),
];

/// The prelude's models of `Eq` whose laws the host admits, by the base type
/// each is the equality of.
const HOSTED: [(&str, BaseType); 2] = [
    ("EqInteger", BaseType::Integer),
    ("EqString", BaseType::String),
];

/// What a definition written as the derivation's call derives.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Derivation
{
    /// `Eq.generic(T)`: the equality.
    Equality,
    /// `Eq.generic.refl(T)` or `Eq.generic.sym(T)`: a law of the equality.
    Law(Statement),
}

/// One definition written `Eq.generic(T)`, `Eq.generic.refl(T)` or
/// `Eq.generic.sym(T)`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Requested<'source>
{
    /// What it derives.
    derivation: Derivation,
    /// The data declaration `T` names.
    data: ConstantIndex,
    /// Where `T` is written.
    named: ByteSpan,
    /// `T` as written.
    name: SurfaceName<'source>,
    /// The call itself, where the derived body is located.
    call: Placed,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Mark the prelude's `Eq.generic` as the derivation it names, and file
    /// the laws the prelude admits of the host's equalities.
    ///
    /// # Specification
    /// - requires: the current source is declared.
    /// - ensures: when the current source is the unit's prelude and exports
    ///   `Eq.generic`, that slot takes [`Role::Generic`] and is remembered, and
    ///   each of `EqInteger`'s and `EqString`'s `refl` and `sym` it exports is
    ///   filed by its base type and law; nothing changes otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point's equality written `Eq.generic(Point)`
    ///   resolves to the marked slot and lowers to the derived declaration, and
    ///   its laws to proofs resting on the host's.
    /// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
    /// - witness: `lower::generic::tests::a_derived_law_lowers_to_its_proof_2302`
    #[spec(ensures: self.generic.is_none_or(|slot| self.collected.slots.get(usize::from(slot)).is_some_and(|entry| entry.role == Role::Generic)))]
    pub(super) fn mark_generic(&mut self)
    {
        let Some(prelude) = self.collected.unit.prelude()
        else {
            return;
        };
        if self.current.source != prelude {
            return;
        }
        let path = NamePath::from(alloc::vec::Vec::from([
            Segment::from(MODULE),
            Segment::from(MEMBER),
        ]));
        let Some(&slot) = self.exported.get(&path)
        else {
            return;
        };
        if let Some(entry) = self.collected.slots.get_mut(usize::from(slot)) {
            entry.role = Role::Generic;
            self.generic = Some(slot);
        }
        for (module, base) in HOSTED {
            for (member, statement) in LAWS {
                let path = NamePath::from(alloc::vec::Vec::from([
                    Segment::from(module),
                    Segment::from(member),
                ]));
                if let Some(&slot) = self.exported.get(&path)
                    && let Some(entry) = self.collected.slots.get(usize::from(slot))
                {
                    self.hosted.push((base, statement, entry.constant));
                }
            }
        }
    }

    /// The derivation a call's head names, when it is `Eq.generic`,
    /// `Eq.generic.refl` or `Eq.generic.sym`.
    ///
    /// # Specification
    /// - requires: `head` is the head operand of the call at `site`.
    /// - ensures: present for a selection `Eq.generic` whose path the namespace
    ///   governs as the prelude module's member, no import alias spelled `Eq`
    ///   standing before it — the equality — and for that selection's `refl` or
    ///   `sym` — the law; absent for any other head, so a source's own `Eq`
    ///   module reads as before.
    /// - fails: the shape reading's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The form refusal of a head the grammar does not hold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the prelude's derivation and its laws are recognised,
    ///   and a source's own `Eq.generic` is not.
    /// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
    /// - witness: `lower::generic::tests::a_derived_law_lowers_to_its_proof_2302`
    /// - witness: `lower::generic::tests::a_source_s_own_eq_module_is_no_derivation_2302`
    #[spec(ensures: |ret| !matches!(ret, Ok(Maybe::Present(_))) || self.generic.is_some())]
    pub(super) fn generic_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Derivation, spelled::Absent>, LoweringRefusal<'source>>
    {
        let unspelled = Ok(Maybe::Absent(spelled::Absent::Unspelled));
        let Some((module, member)) = self.linked_selection(site, head)?
        else {
            return unspelled;
        };
        if self.names_generic(site, module, member).is_some() {
            return Ok(Maybe::Present(Derivation::Equality));
        }
        let written = self.text_at(member);
        let Some(&(_, statement)) = LAWS.iter().find(|&&(name, _)| written.as_ref() == name)
        else {
            return unspelled;
        };
        let Some((inner, derivation)) = self.linked_selection(site, module)?
        else {
            return unspelled;
        };
        if self.names_generic(site, inner, derivation).is_some() {
            return Ok(Maybe::Present(Derivation::Law(statement)));
        }
        unspelled
    }

    /// The module and member a selection `head` links, when it is a
    /// selection the reading did not repair.
    ///
    /// # Specification
    /// - requires: `head` is an operand of the form at `site`.
    /// - ensures: the two linked operands of a projection; none for any other
    ///   form, or one the selection cannot read or read only by repair.
    /// - fails: the shape reading's own refusals.
    /// - panics: none.
    /// - executable: none — the operands are the tree's reading of the
    ///   selection, which no predicate states without reading the pieces again.
    ///
    /// # Errors
    /// The form refusal of a head the grammar does not hold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::generic_head`].
    /// - witness: `lower::generic::tests::a_derived_law_lowers_to_its_proof_2302`
    pub(super) fn linked_selection(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Option<(Placed, Placed)>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(None);
        };
        let Shape::Form {
            former: Former::Projection,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(None);
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, head.node, &mut scratch);
        let linked =
            read.and_then(|()| Self::link(Site { at: head, ..site }, &scratch.pieces, head.span));
        let repaired = matches!(scratch.repair, Maybe::Present(_));
        self.scratch = scratch;
        // A head the selection cannot read is the projection's to refuse.
        Ok(linked.ok().filter(|_| !repaired))
    }

    /// The prelude's derivation, when `module.member`, read at `site`, names
    /// it.
    ///
    /// # Specification
    /// - requires: `module` and `member` are a selection's linked operands.
    /// - ensures: the marked slot exactly when the prelude is marked, `module`
    ///   is a name spelled `Eq` no import alias of the source binds, `member`
    ///   is spelled `generic`, and the namespace governs the path as the
    ///   prelude module's member exported at the marked slot; none otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::generic_head`].
    /// - witness: `lower::generic::tests::a_source_s_own_eq_module_is_no_derivation_2302`
    #[spec(ensures: |ret| ret.is_none() || ret == self.generic)]
    fn names_generic(
        &self,
        site: Site,
        module: Placed,
        member: Placed,
    ) -> Option<SlotIndex>
    {
        let generic = self.generic?;
        let simple = self.tree.node(module.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::Name | Former::Constructor,
                    ..
                })
            )
        });
        let (module_text, member_text) = (self.text_at(module), self.text_at(member));
        if !simple || module_text.as_ref() != MODULE || member_text.as_ref() != MEMBER {
            return None;
        }
        let source = self.collected.unit.source_at(site.at.span.start());
        if let Maybe::Present(_) = self.collected.imports.aliased(source, self.name_at(module)) {
            return None;
        }
        let path = NamePath::from(alloc::vec::Vec::from([
            Segment::from(MODULE),
            Segment::from(MEMBER),
        ]));
        let governed = matches!(
            self.recognition.resolve_path(&path),
            PathResolution::Complete(Recognized::ModuleComponent)
        );
        (governed && self.exported.get(&path) == Some(&generic)).then_some(generic)
    }

    /// Classify `Eq.generic(T)`, or one of its laws, at `site`, the cursor at
    /// its arguments.
    ///
    /// # Specification
    /// - requires: [`Self::generic_head`] recognised the call's head as
    ///   `derivation`.
    /// - ensures: records `derivation` and the data declaration `T` names
    ///   against the declaration whose whole written definition the call is,
    ///   and plans the call [`Plan::Generic`]; `T` and the head are left
    ///   unread.
    /// - fails: other than one argument; the call standing anywhere but as a
    ///   declaration's whole definition; an argument that names no data
    ///   declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] with the arity boundary for the
    /// argument count; [`LoweringRefusal::GenericMisplaced`] at the call
    /// otherwise; the name resolution's own refusals.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition written as the call records its data
    ///   declaration; the call inside a larger body, and over a function, are
    ///   each refused misplaced.
    /// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
    /// - witness: `lower::generic::tests::a_derived_law_lowers_to_its_proof_2302`
    /// - witness: `lower::generic::tests::a_misplaced_generic_is_refused_at_the_call_2302`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Generic)))]
    pub(super) fn generic_call(
        &mut self,
        site: Site,
        derivation: Derivation,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let misplaced = LoweringRefusal::GenericMisplaced { span: site.at.span };
        let frame = self.require(site, Produced::Value)?;
        let [argument] = exactly(site, &mut cursor, &mut self.operands)?;
        let Maybe::Present(owner) = self.collected.owner_of(site.at.node)
        else {
            return Err(misplaced);
        };
        let whole = site.reading == Reading::Value(Frame::Outermost)
            && self
                .collected
                .slots
                .get(usize::from(owner))
                .is_some_and(|slot| {
                    matches!(
                        slot.definition,
                        Maybe::Present(Half { operand: Operand::Written(written), .. })
                            if written.node == site.at.node
                    )
                });
        if !whole {
            return Err(misplaced);
        }
        let Some(node) = self.tree.node(argument)
        else {
            return Err(misplaced);
        };
        let at = Placed::of(argument, node);
        let Shape::Form {
            former: Former::Name | Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Err(misplaced);
        };
        let name = self.name_at(at);
        let Maybe::Present(Resolved::Declaration { constant, .. }) =
            self.resolve_name(Site { at, ..site }, frame, name)?
        else {
            return Err(misplaced);
        };
        let data = self
            .collected
            .slots
            .get(usize::from(constant))
            .is_some_and(|slot| {
                matches!(
                    slot.definition,
                    Maybe::Present(Half {
                        operand: Operand::Data(_),
                        ..
                    })
                )
            });
        if !data {
            return Err(misplaced);
        }
        let _first = self.requested.insert(owner, Requested {
            derivation,
            data: constant,
            named: at.span,
            name,
            call: site.at,
        });
        self.plan(site, Plan::Generic);
        Ok(())
    }

    /// Mint what each definition of the current source written
    /// `Eq.generic(T)`, `Eq.generic.refl(T)` or `Eq.generic.sym(T)` derives.
    ///
    /// # Specification
    /// - requires: the current source's data declarations are minted.
    /// - ensures: each such slot holding no refusal is minted to its declared
    ///   type — the written signature's when it states one, the derived one
    ///   otherwise, located at the declaration — and the derived body, located
    ///   at the call, where a hover answers it; or refused
    ///   [`LoweringRefusal::GenericUncovered`] at `T` with what the derivation
    ///   does not cover. The derivation reads each declaration off its
    ///   levitated code ([`Self::coded`]), never its admitted signature. A
    ///   law's integer and string fields rest on the laws the prelude admits of
    ///   the host's equalities.
    /// - panics: none.
    /// - executable: none — the derived declaration is the checker's to judge.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point's and a recursive declaration's equalities
    ///   mint and check, and a point's laws; a declaration with a function
    ///   field is refused, and a law over a flag.
    /// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
    /// - witness: `lower::generic::tests::a_derived_law_lowers_to_its_proof_2302`
    /// - witness: `lower::generic::tests::an_uncovered_declaration_is_refused_at_its_name_2302`
    #[cfg_attr(feature = "hotpath", hotpath::measure(impl_type = "Lowerer"))]
    pub(super) fn mint_generics(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let requested: Vec<(SlotIndex, Requested<'source>)> = self
            .requested
            .range(SlotIndex::from(self.current.slots) ..)
            .map(|(&slot, &request)| (slot, request))
            .collect();
        if requested.is_empty() {
            return;
        }
        // The host's laws, minted once for every law the source derives.
        let hosted: Vec<_> = if requested
            .iter()
            .any(|&(_, request)| matches!(request.derivation, Derivation::Law(_)))
        {
            self.hosted
                .iter()
                .map(|&(base, stated, constant)| {
                    (base, stated, sink.arena.value_constant(constant))
                })
                .collect()
        }
        else {
            Vec::new()
        };
        // Each declaration the derivations reach, read off its levitated code.
        let coded = self.coded(
            sink.arena,
            requested.iter().map(|&(_, request)| request.data),
        );
        for (slot, request) in requested {
            let Some(entry) = self.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let origin = Origin::new(entry.named.node, entry.named.span);
            let written = match entry.signature {
                Maybe::Present(Half {
                    operand: Operand::Written(written),
                    ..
                }) => self.value_type_at(written.node),
                Maybe::Present(_) | Maybe::Absent(_) => {
                    Maybe::Absent(super::lowered::Absent::Unminted)
                },
            };
            let lookup = |constant: ConstantIndex| -> Result<&DataSignature, Uncovered> {
                match coded.get(&constant) {
                    Some(&Ok(ref signature)) => Ok(signature),
                    Some(&Err(fault)) => Err(fault),
                    None => Err(Uncovered::Unknown(constant)),
                }
            };
            let derived = match request.derivation {
                Derivation::Equality => equality(sink.arena, request.data, &lookup),
                Derivation::Law(statement) => law(
                    sink.arena,
                    request.data,
                    &lookup,
                    statement,
                    &|base, wanted| {
                        hosted
                            .iter()
                            .find(|&&(at, stated, _)| at == base && stated == wanted)
                            .map(|&(_, _, constant)| constant)
                    },
                ),
            };
            match derived {
                Ok(derived) => {
                    // A written signature keeps the origin its own lowering
                    // recorded; only the type the derivation minted is new.
                    let declared = match written {
                        Maybe::Present(stated) => stated,
                        Maybe::Absent(_) => {
                            sink.origins.record_value_type(derived.declared(), origin);
                            derived.declared()
                        },
                    };
                    sink.origins.record_value(
                        derived.body(),
                        Origin::new(request.call.node, request.call.span),
                    );
                    // Each case names the declaration it eliminates, so its
                    // branches read as that declaration's constructors.
                    for &(case, family) in derived.cases() {
                        sink.origins.record_elimination(case, family);
                    }
                    let _first = self.generics.insert(slot, (declared, derived.body()));
                },
                Err(fault) => {
                    let _first = self.faults.insert(slot, LoweringRefusal::GenericUncovered {
                        span: request.named,
                        data: request.name,
                        fault,
                    });
                },
            }
        }
    }

    /// Each data declaration the requested derivations reach, read off its
    /// levitated code: the constructor table the code decodes to, or why it
    /// has none.
    ///
    /// # Specification
    /// - requires: every source so far is collected, its descriptions read.
    /// - ensures: each of `roots` holds the answer [`Self::code_of`] states,
    ///   and so does each data declaration a decoded field names, directly or
    ///   inside a product or a sum.
    /// - fails: never; a declaration with no code holds the reason.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: a position is read at most once, and only an unanswered one.
    /// - measure: the collected slots not yet answered.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursive declaration, one whose fields name two
    ///   others and one with a function field each answer as their codes state.
    /// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
    /// - witness: `lower::generic::tests::an_uncovered_declaration_is_refused_at_its_name_2302`
    #[spec(ensures: |ret| ret.values().all(|answer| answer.as_ref().map_or(true, |signature| signature.parameters().is_empty())))]
    fn coded(
        &self,
        arena: &mut CoreArena,
        roots: impl IntoIterator<Item = ConstantIndex>,
    ) -> BTreeMap<ConstantIndex, Result<DataSignature, Uncovered>>
    {
        let mut names = self.code_names();
        let mut coded = BTreeMap::new();
        let mut pending: Vec<ConstantIndex> = roots.into_iter().collect();
        let mut types: Vec<ValueTypeId> = Vec::new();
        while let Some(position) = pending.pop() {
            if coded.contains_key(&position) {
                continue;
            }
            let read = self.code_of(arena, position, &mut names);
            if let Ok(ref signature) = read {
                types.extend(signature.constructors().iter().flatten().copied());
                while let Some(ty) = types.pop() {
                    match arena.value_type(ty) {
                        Some(&ValueType::Data { declaration, .. }) => pending.push(declaration),
                        Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                            types.extend(parts.iter().copied());
                        },
                        Some(_) | None => {},
                    }
                }
            }
            let _first = coded.insert(position, read);
        }
        coded
    }

    /// The type each data declaration's name stands for in a code's leaves:
    /// the declaration itself at its parameter count, the first declared of a
    /// name winning, as the levitated universe reads a family by its name. A
    /// source's declaration wins over the prelude's, as the prelude answers
    /// only a name no source declares.
    ///
    /// # Specification
    /// - requires: every source so far is collected.
    /// - ensures: one nominal binding per name some data declaration with a
    ///   description or a native reading carries: the first a source other than
    ///   the prelude declares, else the prelude's.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field naming another declaration decodes to that
    ///   declaration, and to a source's own where the prelude declares the name
    ///   too.
    /// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
    /// - witness: `lower::generic::tests::a_leaf_reads_a_source_s_family_before_the_prelude_s_3287`
    #[spec(ensures: |ret| ret.values().all(|binding| matches!(binding, TypeBinding::Nominal { .. })))]
    fn code_names(&self) -> BTreeMap<Name, TypeBinding>
    {
        let natives: BTreeMap<NodeIndex, &NativeFamily> = self
            .collected
            .natives
            .iter()
            .map(|native| (native.named.node, native))
            .collect();
        let mut names = BTreeMap::new();
        let prelude = self.collected.unit.prelude();
        let preluded = |slot: &&DeclarationSlot<'source>| {
            prelude.is_some_and(|prelude| {
                self.collected.unit.source_at(slot.named.span.start()) == prelude
            })
        };
        let (laid, written): (Vec<_>, Vec<_>) = self.collected.slots.iter().partition(preluded);
        for slot in written.into_iter().chain(laid) {
            let Maybe::Present(Half {
                operand: Operand::Data(_),
                ..
            }) = slot.definition
            else {
                continue;
            };
            let (name, arity) = if let Maybe::Present(entry) =
                self.collected.descriptions.get(&slot.introduced_by.node)
            {
                (&entry.description.id.name, entry.parameters.len())
            }
            else if let Some(native) = natives.get(&slot.named.node) {
                (&native.name, native.parameters.len())
            }
            else {
                continue;
            };
            let _held = names.entry(name.clone()).or_insert(TypeBinding::Nominal {
                declaration: slot.constant,
                arity: TypeArity(arity),
            });
        }
        names
    }

    /// The data declaration at `position` read off its levitated code: each
    /// constructor's product spine flattened into its fields, a `var` of the
    /// family the recursion, and each leaf interpreted at the type it names,
    /// a builtin type head entered into `names` as it is met.
    ///
    /// # Specification
    /// - requires: `names` holds [`Self::code_names`]'s bindings.
    /// - ensures: the constructor table of a closed, free, unpresented family
    ///   with a code, at its classifier, with no parameters; constructor order
    ///   is tag order.
    /// - fails: [`Uncovered::Unknown`] for no data declaration,
    ///   [`Uncovered::Applied`] for parameters or indices,
    ///   [`Uncovered::Presented`] for rules, and for a family the native
    ///   reading owns whole, or a leaf the decoder does not read, the first
    ///   field the code cannot carry: [`Uncovered::Field`] for a function,
    ///   [`Uncovered::Dependent`] for a field reading one before it, and
    ///   [`Uncovered::Uncoded`] for any other.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: each step pops one code node and pushes only its two factors.
    /// - measure: the code nodes not yet popped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursive family reads its `var`, a family naming
    ///   others reads their declarations and a builtin, and a function field
    ///   refuses at its site.
    /// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
    /// - witness: `lower::generic::tests::an_uncovered_declaration_is_refused_at_its_name_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |signature| signature.parameters().is_empty() && signature.indices().is_empty()))]
    fn code_of(
        &self,
        arena: &mut CoreArena,
        position: ConstantIndex,
        names: &mut BTreeMap<Name, TypeBinding>,
    ) -> Result<DataSignature, Uncovered>
    {
        let unknown = Uncovered::Unknown(position);
        let slot = self
            .collected
            .slots
            .get(usize::from(position))
            .ok_or(unknown)?;
        let Maybe::Present(Half {
            operand: Operand::Data(_),
            ..
        }) = slot.definition
        else {
            return Err(unknown);
        };
        let Maybe::Present(entry) = self.collected.descriptions.get(&slot.introduced_by.node)
        else {
            return Err(self
                .collected
                .natives
                .iter()
                .find(|native| native.named.node == slot.named.node)
                .and_then(|native| uncarried(position, native))
                .unwrap_or(unknown));
        };
        if !entry.parameters.is_empty()
            || entry
                .written
                .constructors
                .iter()
                .any(|written| written.arguments.len() > entry.parameters.len())
        {
            return Err(Uncovered::Applied(position));
        }
        if !entry.description.rules.is_empty() {
            return Err(Uncovered::Presented(position));
        }
        let Maybe::Present(classifier) = entry.classifier
        else {
            return Err(unknown);
        };
        let Maybe::Present(kind) = self.value_type_at(classifier.node)
        else {
            return Err(unknown);
        };
        let family = &entry.description.id.name;
        let own = arena.value_type_data(position, Vec::new());
        let mut constructors = Vec::with_capacity(entry.description.ctors.len());
        let mut pending = Vec::new();
        for (tag, constructor) in entry.description.ctors.iter().enumerate() {
            let mut fields = Vec::new();
            pending.push(constructor.code.to_node());
            while let Some(node) = pending.pop() {
                let uncoded = Uncovered::Uncoded(position, OccurrenceSite::Field {
                    tag: ConstructorTag::from(tag),
                    field: FieldPosition::from(fields.len()),
                });
                match node.view() {
                    CodeView::Unit => {},
                    CodeView::Prod(mut factors) => {
                        let (Some(left), Some(right)) = (factors.next(), factors.next())
                        else {
                            return Err(uncoded);
                        };
                        pending.push(right);
                        pending.push(left);
                    },
                    CodeView::Var(sort) if sort == family => fields.push(own),
                    CodeView::Field { ty, .. } => {
                        enter_builtins(arena, ty, names);
                        let context = DecodeContext {
                            self_sort: NameRef::from(family.as_ref()),
                            self_type: own,
                            depth: ParameterDepth(0),
                            locals: &[],
                            types: names,
                        };
                        fields.push(decode_ref(arena, ty, context).map_err(|_unread| uncoded)?);
                    },
                    // A function has no equality, as the native reading
                    // answers for the same field.
                    CodeView::Fun { .. } => {
                        return Err(Uncovered::Field(position, OccurrenceSite::Field {
                            tag: ConstructorTag::from(tag),
                            field: FieldPosition::from(fields.len()),
                        }));
                    },
                    CodeView::Var(_) | CodeView::Sum(_) | CodeView::Bind { .. } => {
                        return Err(uncoded);
                    },
                }
            }
            constructors.push(fields);
        }
        Ok(DataSignature::new(Vec::new(), constructors, kind))
    }
}

/// Enter into `names` each builtin type head `ty` writes that no
/// declaration's name already binds, at the type it stands for.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every head of `ty` the builtin table answers is bound; no binding
///   already held changes.
/// - fails: never; a head neither binds is left for the decoder to refuse.
/// - panics: none.
///
/// # Termination
/// - reason: each step pops one type node and pushes only its arguments.
/// - measure: the type nodes not yet popped.
///
/// # Adequacy
/// - hypothesis: L3 — a flag written `Bool` decodes to the boolean.
/// - witness: `lower::generic::tests::a_generic_equality_lowers_to_the_derived_declaration_2302`
#[spec(captures: [before = names.len()], ensures: names.len() >= before)]
fn enter_builtins(
    arena: &mut CoreArena,
    ty: &ValueTypeRef,
    names: &mut BTreeMap<Name, TypeBinding>,
)
{
    let mut pending = vec![ty.to_node()];
    while let Some(node) = pending.pop() {
        let ValueTypeView::Ctor { head, args } = node.view()
        else {
            continue;
        };
        pending.extend(args);
        if names.contains_key(head) {
            continue;
        }
        if let Maybe::Present(atom) = type_atom(SurfaceName::from(head.as_ref())) {
            let _first = names.insert(head.clone(), TypeBinding::Type(atom_type(arena, atom)));
        }
    }
}

/// The fault a family the native reading owns whole answers a derivation
/// with, at the first constructor field its code cannot carry: a function
/// has no equality, a field reading one before it is dependent, and any other
/// is a type the code does not carry.
///
/// # Specification
/// - requires: `native` is the family at `position`.
/// - ensures: the fault at the field whose written type holds the first
///   uncarried field's site; none when no written field holds it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function field refuses as a field with no equality.
/// - witness: `lower::generic::tests::an_uncovered_declaration_is_refused_at_its_name_2302`
#[spec(ensures: |ret| ret.is_none_or(|fault| matches!(fault, Uncovered::Field(at, _) | Uncovered::Dependent(at, _) | Uncovered::Uncoded(at, _) if at == position)))]
fn uncarried(
    position: ConstantIndex,
    native: &NativeFamily,
) -> Option<Uncovered>
{
    let diagnostic = native.uncoded.first()?;
    let at = diagnostic.span.start();
    native
        .written
        .constructors
        .iter()
        .enumerate()
        .find_map(|(tag, written)| {
            let field = written.fields.iter().position(|field| {
                let from = match field.named {
                    Maybe::Present(named) => named.start(),
                    Maybe::Absent(_) => field.sort.span.start(),
                };
                from <= at && at < field.sort.span.end()
            })?;
            let site = OccurrenceSite::Field {
                tag: ConstructorTag::from(tag),
                field: FieldPosition::from(field),
            };
            Some(match diagnostic.fault {
                DescriptionFault::HigherOrderField => Uncovered::Field(position, site),
                DescriptionFault::DependentField => Uncovered::Dependent(position, site),
                DescriptionFault::Malformed
                | DescriptionFault::Repaired { .. }
                | DescriptionFault::FamilyHead
                | DescriptionFault::NonUniformResult
                | DescriptionFault::GeneratorJudgment
                | DescriptionFault::MemberPolarity
                | DescriptionFault::TypeShape
                | DescriptionFault::RetiredRuleArrow
                | DescriptionFault::RetiredOperation
                | DescriptionFault::NativeDecode(_)
                | DescriptionFault::IllFormed(_)
                | DescriptionFault::Signature(_) => Uncovered::Uncoded(position, site),
            })
        })
}
