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
//! - A definition that also states its type is checked at the stated type, so a
//!   signature that disagrees with the derived equality or law is refused where
//!   it was written; a model's law is checked so at its theory's statement.

use anodized::spec;
use gandr_core_term::DataSignature;
use gandr_core_term::generic::equality;
use gandr_core_term::generic::law::Statement;
use gandr_core_term::generic::law::law;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::ByteSpan;
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
use super::arguments;
use super::identity::spelled;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::module::Half;
use crate::module::Operand;
use crate::module::Role;
use crate::module::SlotIndex;
use crate::origin::Origin;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

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
        let start = self.operands.len();
        let read = arguments(site, &mut cursor, &mut self.operands);
        let count = self.operands.len().saturating_sub(start);
        let first = self.operands.get(start).copied();
        self.operands.truncate(start);
        read?;
        let (1_usize, Some(argument)) = (count, first)
        else {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        };
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
    ///   does not cover. A law's integer and string fields rest on the laws the
    ///   prelude admits of the host's equalities.
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
        let requested: alloc::vec::Vec<(SlotIndex, Requested<'source>)> = self
            .requested
            .range(SlotIndex::from(self.current.slots) ..)
            .map(|(&slot, &request)| (slot, request))
            .collect();
        // The host's laws, minted once for every law the source derives.
        let hosted: alloc::vec::Vec<_> = if requested
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
            alloc::vec::Vec::new()
        };
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
            let lookup = |constant: ConstantIndex| -> Option<&DataSignature> {
                let Maybe::Present(Half {
                    operand: Operand::Data(form),
                    ..
                }) = self.collected.slots.get(usize::from(constant))?.definition
                else {
                    return None;
                };
                let &index = self.signatures.get(&form)?;
                self.data
                    .get(usize::from(index))
                    .map(|signature| &**signature)
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
}
