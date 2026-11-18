//! Declarations of the native table's rows, as the lowering reads them.
//!
//! A signature with no definition owes its value. `std` declares each
//! operation of the native table this way, and a `native` mark names the row:
//!
//! ```text
//! @[native("string.append")]
//! pub def append : String -> String -> String;
//! ```
//!
//! The row gives the value, so the signature owes nothing. A name of the
//! declaration lowers as the row's own name lowers, so a call of the
//! declaration is the call of the row, and the lowered program does not
//! change. The declared type is the row's type, or the mark is refused.
//!
//! - see: #7961

use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::equal_type_syntax;
use gandr_core_term::primitive::PRELUDE;
use gandr_kernel_term::Literal;
use quenchant_shape::shape::Maybe;

use super::Expressions;
use super::Families;
use super::Sink;
use crate::attribute::RegisteredAttribute;
use crate::error::LoweringRefusal;
use crate::error::NativeFault;
use crate::form::Former;
use crate::module::Half;
use crate::module::Operand;
use crate::module::Payload;
use crate::module::SlotIndex;
use crate::origin::Origin;

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Read the row that each `native` mark of the current source names.
    ///
    /// # Specification
    /// - requires: the collection declared the current source's slots, and
    ///   their written attributes stand on them.
    /// - ensures: each slot of the current source that holds no refusal and
    ///   carries a `native` mark takes the row its text names in the context's
    ///   natives. The mark is refused by name instead when its text names no
    ///   row, when the slot has a body, when the source is no module of `std`,
    ///   or when an earlier slot declares the row.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a marked signature takes its row, and each fault
    ///   takes its own refusal.
    /// - witness: `gandr-surface-lowering::lower::row::tests::a_native_signature_lowers_to_its_row_7961`
    /// - witness: `gandr-surface-lowering::lower::row::tests::a_faulty_native_mark_is_refused_by_name_7961`
    pub fn read_natives(&mut self)
    {
        let cx = self.cx_mut();
        let homed = matches!(cx.collected.unit.home(cx.current.source), Maybe::Present(_));
        let mut read = Vec::new();
        for (index, slot) in cx.collected.slots.iter().enumerate().skip(cx.current.slots) {
            if let Maybe::Present(_) = slot.refusal {
                continue;
            }
            let Some(mark) = slot
                .attributes
                .iter()
                .find(|written| written.name.as_ref() == RegisteredAttribute::NATIVE.as_ref())
            else {
                continue;
            };
            let row = match mark.payload {
                Payload::Written(text) => {
                    match crate::lower::parse_literal(Former::Text, cx.text_at(text)) {
                        Maybe::Present(Literal::Text(row)) => PRELUDE
                            .iter()
                            .find(|primitive| primitive.name().as_ref() == row.as_ref())
                            .copied(),
                        Maybe::Present(_) | Maybe::Absent(_) => None,
                    }
                },
                Payload::Unwritten => None,
            };
            let found = match (row, slot.definition, homed) {
                (None, ..) => Err(NativeFault::NoRow),
                (Some(_), Maybe::Present(_), _) => Err(NativeFault::Bodied),
                (Some(_), Maybe::Absent(_), false) => Err(NativeFault::OutsideStd),
                (Some(primitive), Maybe::Absent(_), true) => Ok(primitive),
            };
            read.push((SlotIndex::from(index), mark.at.node, mark.span, found));
        }
        for (slot, node, span, found) in read {
            let fault = match found {
                Ok(primitive) if cx.natives.values().any(|&held| held == primitive) => {
                    NativeFault::SecondDeclaration
                },
                Ok(primitive) => {
                    let _first = cx.natives.insert(slot, primitive);
                    continue;
                },
                Err(fault) => fault,
            };
            if let Some(entry) = cx.collected.slots.get_mut(usize::from(slot)) {
                entry.refuse(node, LoweringRefusal::NativeMark { span, fault });
            }
        }
    }

    /// Mint the declared type and the row's value of each `native`
    /// signature of the current source.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so each signature's type is minted.
    /// - ensures: each slot of the current source in the context's natives,
    ///   holding no refusal, whose minted type is the row's type, takes that
    ///   type and the row's thunk in the context's natived. A slot whose minted
    ///   type differs takes the refusal of its mark instead.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::read_natives`].
    /// - witness: `gandr-surface-lowering::lower::row::tests::a_native_signature_lowers_to_its_row_7961`
    /// - witness: `gandr-surface-lowering::lower::row::tests::a_faulty_native_mark_is_refused_by_name_7961`
    pub fn mint_natives(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let cx = self.cx_mut();
        let mut minted = Vec::new();
        for (&slot, &primitive) in cx.natives.range(SlotIndex::from(cx.current.slots) ..) {
            let Some(entry) = cx.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let Maybe::Present(Half {
                operand: Operand::Written(written),
                ..
            }) = entry.signature
            else {
                continue;
            };
            let Maybe::Present(declared) = cx.value_type_at(written.node)
            else {
                continue;
            };
            let computation = primitive.declared_type(sink.arena);
            let row = sink.arena.value_type_thunk(computation);
            if equal_type_syntax(sink.arena, row, declared) == CertificateEquality::Equal {
                let origin = Origin::new(entry.named.node, entry.named.span);
                let body = primitive.thunk(sink.arena);
                let _value = sink.value(body, origin);
                minted.push((slot, Ok((declared, body))));
            }
            else if let Some(mark) = entry
                .attributes
                .iter()
                .find(|written| written.name.as_ref() == RegisteredAttribute::NATIVE.as_ref())
            {
                minted.push((
                    slot,
                    Err(LoweringRefusal::NativeMark {
                        span: mark.span,
                        fault: NativeFault::TypeDiffers,
                    }),
                ));
            }
        }
        for (slot, found) in minted {
            match found {
                Ok(completed) => {
                    let _first = cx.natived.insert(slot, completed);
                },
                Err(refusal) => {
                    let _first = cx.faults.insert(slot, refusal);
                },
            }
        }
    }
}
