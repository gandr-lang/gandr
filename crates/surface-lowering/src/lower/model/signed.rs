//! An import written at a signature, `import hello : Greeting ;` (#3098): the
//! source's `pub` interface, which its `pub` declarations infer (#533's ruling
//! of 2026-10-26), is matched against the theory the import names, member by
//! member, by name and by type.
//!
//! Each operation or constant of the signature needs a `pub` declaration of
//! its name at the top of the imported source, written at the type the member
//! derives as a model component: the type a module ascribed `Model(T)` checks
//! the member at (#746), read with no sort of `T` fixed. The two types are
//! compared as syntax, so the match is decided where the import is lowered,
//! before anything reads through it. A signature naming fewer members than
//! the interface holds settles; one naming a member the source does not
//! export, or holds at another type, refuses every declaration of the
//! importing source at the import, naming the member, as an import whose list
//! names what its module does not declare refuses them.
//!
//! The match reads written types only. A declaration with no signature has no
//! type before the checker synthesises one, and a signature's sort, law or
//! nested model has no type the match compares, so either is refused as
//! unstated rather than matched by name alone. The match is coercive (the
//! record's `module-and-package-design.md` § invariants): the import binds
//! the signature's members and no other, so a name the signature does not
//! state is unknown through the import even where the source exports it.
//!
//! # Alternatives and reversal
//!
//! - Matching through the checker, the import's reads each ascribed the
//!   member's type: declined, because a mismatch would then be the checker's
//!   type error at each read rather than a refusal at the import, and an unread
//!   member would never be matched at all.
//! - A stated advertisement, an interface file or an ascription of the root
//!   (#587): the follow-on, ascribed against the inferred interface this match
//!   reads.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ValueTypeId;
use gandr_core_term::equal_type_syntax;
use quenchant_shape::shape::Maybe;

use super::Fields;
use super::Members;
use super::Minting;
use crate::error::LoweringRefusal;
use crate::error::MatchFault;
use crate::import::ImportResolution;
use crate::import::ImportSignature;
use crate::lower::DeclarationOutcome;
use crate::lower::Lowerer;
use crate::lower::Sink;
use crate::model::ModelForm;
use crate::model::derive;
use crate::module::Container;
use crate::module::SlotIndex;
use crate::module::Visibility;
use crate::origin::Origin;
use crate::resolve::SurfaceName;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;

/// What the match of a signature against an interface came to, when it does
/// not hold.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unmatched<'source>
{
    /// A member the interface does not hold, and how.
    Member(SurfaceName<'source>, MatchFault),
    /// The signature names no theory the import's source reads: the refusal
    /// naming the theory's name.
    Unnamed(LoweringRefusal<'source>),
}

impl<'source> Lowerer<'_, 'source>
{
    /// Refuse every declaration of the current source whose import is
    /// written at a signature its source's `pub` interface does not hold.
    ///
    /// # Specification
    /// - requires: the current source's collection and mint have run, and its
    ///   imports' sources are lowered.
    /// - ensures: for each import of the current source written at a signature
    ///   and resolved to a source, every slot whose name stands in the current
    ///   source holds, as a fault, the first refusal [`Self::unmatched`] finds:
    ///   [`LoweringRefusal::SignatureMismatch`] at the signature's name, naming
    ///   the member, or the refusal of a signature naming no theory. A slot
    ///   already refused, or already faulted, keeps its own.
    /// - fails: never; a refusal is carried by each declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an import at the interface whole and one at fewer
    ///   members settle; one at a member the source lacks, one at another type
    ///   and one at a member the source writes no type for refuse each
    ///   declaration of the importer by name.
    /// - witness: `tests::namespace::an_import_at_a_narrower_signature_settles_3098`
    /// - witness: `tests::namespace::an_import_at_a_wider_signature_refuses_its_source_3098`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: self.collected.slots.len() == before,
    )]
    pub(in crate::lower) fn match_signatures(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let source = self.current.source;
        let mut refusals = Vec::new();
        for import in self.collected.imports.declarations() {
            let (
                &Maybe::Present(ref signature),
                ImportResolution::Path(ImportTarget::Source(target)),
            ) = (import.signature(), import.resolution())
            else {
                continue;
            };
            if import.source() != source {
                continue;
            }
            if let Maybe::Present(unmatched) = self.unmatched(signature, target, sink) {
                refusals.push((signature.clone(), unmatched));
            }
        }
        for (signature, unmatched) in refusals {
            for (index, slot) in self.collected.slots.iter().enumerate() {
                if self.collected.unit.source_at(slot.named.span.start()) != source
                    || matches!(slot.refusal, Maybe::Present(_))
                {
                    continue;
                }
                let refusal = match unmatched {
                    Unmatched::Member(member, fault) => LoweringRefusal::SignatureMismatch {
                        span: signature.named.span,
                        signature: signature.name,
                        member,
                        fault,
                        refused: slot.named.span,
                    },
                    Unmatched::Unnamed(refusal) => refusal,
                };
                let _first = self.faults.entry(SlotIndex::from(index)).or_insert(refusal);
            }
        }
    }

    /// The first member of `signature` the `pub` interface of `target` does
    /// not hold, in the signature's order.
    ///
    /// # Specification
    /// - requires: `target` is lowered.
    /// - ensures: absent when every member of the theory `signature` names is
    ///   an operation or a constant whose name a `pub` declaration at the top
    ///   of `target` bears, that declaration's written type syntactically the
    ///   type the member derives with no sort fixed; otherwise the first member
    ///   that is not: [`MatchFault::Missing`] for one no `pub` declaration
    ///   bears, [`MatchFault::Sort`] for one written at another type, and
    ///   [`MatchFault::Unstated`] for one with no written type, or that is a
    ///   sort, a law or a nested model, or whose type does not mint. A theory
    ///   the signature does not name, or that presents no model signature, is
    ///   the refusal its lookup gives, or unstated at the theory's name.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the verdict is the match itself, member by member
    ///   over the derived signature and the target's slots; a clause would
    ///   restate it whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::match_signatures`].
    /// - witness: `tests::namespace::an_import_at_a_wider_signature_refuses_its_source_3098`
    fn unmatched(
        &self,
        signature: &ImportSignature<'source>,
        target: SourceIndex,
        sink: &mut Sink<'_>,
    ) -> Maybe<Unmatched<'source>, matched::Absent>
    {
        let named = signature.named;
        let presentation = match self.collected.presented_theory_in(
            named.span.start(),
            &signature.prefix,
            named.span,
            signature.name,
        ) {
            Ok((_, presentation)) => presentation,
            Err(refusal) => return Maybe::Present(Unmatched::Unnamed(refusal)),
        };
        let Ok(derived) = derive(presentation)
        else {
            return Maybe::Present(Unmatched::Member(signature.name, MatchFault::Unstated));
        };
        let minting = Minting {
            members: Members::Fields(Fields {
                before: &[],
                binds: &[],
                manifests: &[],
            }),
            origin: Origin::new(named.node, named.span),
        };
        for component in &derived.components {
            let member = self.name_at(component.named);
            let fault = |fault| Maybe::Present(Unmatched::Member(member, fault));
            let Some(position) = self
                .collected
                .by_name
                .get(&(Container::TopLevel(target), member))
                .copied()
                .filter(|&position| self.collected.slot_visibility(position) == Visibility::Public)
            else {
                return fault(MatchFault::Missing);
            };
            let Ok(ref form @ (ModelForm::Operation { .. } | ModelForm::Constant(_))) =
                component.form
            else {
                return fault(MatchFault::Unstated);
            };
            let Maybe::Present(declared) = self.written_type(position)
            else {
                return fault(MatchFault::Unstated);
            };
            let Ok(expected) = self.mint_form(form, &minting, sink)
            else {
                return fault(MatchFault::Unstated);
            };
            if equal_type_syntax(sink.arena, expected, declared) != CertificateEquality::Equal {
                return fault(MatchFault::Sort);
            }
        }

        Maybe::Absent(matched::Absent::Held)
    }

    /// The type the declaration at `position` is written at.
    ///
    /// # Specification
    /// - requires: the declaration's source is lowered.
    /// - ensures: the declared type of a declaration whose outcome carries one,
    ///   completed or not; absent for one that has none — a definition with no
    ///   signature, a refused declaration, a family or a module.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::match_signatures`].
    /// - witness: `tests::namespace::an_import_at_a_wider_signature_refuses_its_source_3098`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || usize::from(position) < self.collected.slots.len())]
    fn written_type(
        &self,
        position: SlotIndex,
    ) -> Maybe<ValueTypeId, unwritten::Absent>
    {
        let Some(slot) = self.collected.slots.get(usize::from(position))
        else {
            return Maybe::Absent(unwritten::Absent::Unwritten);
        };
        match self.outcome(position, slot) {
            Maybe::Present(
                DeclarationOutcome::Completed { declared_type, .. }
                | DeclarationOutcome::Uncompleted { declared_type },
            ) => Maybe::Present(declared_type),
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(unwritten::Absent::Unwritten),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a signature's match finds nothing to refuse.
    mod matched {
        /// The reason the match holds.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The interface holds every member at the member's type.
            Held,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration has no written type the match reads.
    mod unwritten {
        /// The reason none is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Its outcome carries no declared type.
            Unwritten,
        }
    }
}
