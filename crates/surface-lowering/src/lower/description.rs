//! Described families the native data reading does not own, decoded from the
//! same descriptions exposed to cell consumers.
//!
//! A data declaration form has one producer of its signature: the native
//! reading, which also enters its constructors and compiles its matches. Its
//! description is checked and elaborated to cells beside it. Every other
//! described family — codata today — reaches the decoder here, whose refusal
//! is reported at the family. Reversal: a description decode that agrees with
//! the native reading on every data form can replace it as the producer.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Zone;
use gandr_core_term::description::DecodeContext;
use gandr_core_term::description::DecodeError;
use gandr_core_term::description::LocalBinding;
use gandr_core_term::description::ParameterDepth;
use gandr_core_term::description::ParameterLevel;
use gandr_core_term::description::TypeArity;
use gandr_core_term::description::TypeBinding;
use gandr_core_term::description::decode_signature;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Reading;
use super::Sink;
use crate::FragmentBoundary;
use crate::FragmentSort;
use crate::LoweringRefusal;
use crate::description::DescribedDeclaration;
use crate::description::DescriptionDiagnostic;
use crate::description::DescriptionFault;
use crate::form::Former;
use crate::form::Shape;
use crate::form::shape_of;
use crate::module::DataIndex;
use crate::module::SlotIndex;
use crate::resolve::Frame;

/// Whether the native data reading owns a described declaration.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct NativelyRead(bool);

impl<'source> Lowerer<'_, 'source>
{
    /// Whether the native data reading owns the described declaration
    /// `entry`: a data declaration form, which it reads whole.
    ///
    /// # Specification
    /// - requires: `entry` was described from this lowering run's tree.
    /// - ensures: true exactly when the entry's form is a data declaration.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a data family keeps its native signature while a
    ///   codata family beside it reaches the decoder and is refused there.
    /// - witness: `description::tests::native_data_keeps_telescope_and_nominal_heads`
    /// - witness: `description::tests::codata_is_refused_by_the_decoder_and_data_beside_it_is_native`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    fn natively_read(
        &self,
        entry: &DescribedDeclaration,
    ) -> Result<NativelyRead, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(entry.at.node)
        else {
            return Ok(NativelyRead(false));
        };
        Ok(NativelyRead(matches!(
            shape_of(self.pbg, node)?,
            Shape::Form {
                former: Former::Data,
                ..
            }
        )))
    }

    /// Seed the parameters of every described family the native reading does
    /// not own: each parameter's type under the parameters before it.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: one frame per parameter, typed with its written type and
    ///   mentioned, and one seed per parameter type, appended to `seeds`; a
    ///   data declaration form is left to [`Self::seed_data`].
    /// - provides: the description half of [`Self::seed`].
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameterised codata family reaches the decoder
    ///   with its parameter types minted, and a data family beside it is seeded
    ///   once, natively.
    /// - witness: `description::tests::codata_is_refused_by_the_decoder_and_data_beside_it_is_native`
    #[spec(
        captures: before = seeds.len(),
        ensures: |ret| ret.is_err() || seeds.len() >= before,
    )]
    pub(super) fn seed_descriptions(
        &mut self,
        seeds: &mut Vec<(NodeIndex, Reading)>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for entry in self.collected.descriptions.values() {
            if self.natively_read(entry)?.0 {
                continue;
            }
            let mut frame = Frame::Outermost;
            for parameter in &entry.parameters {
                seeds.push((parameter.classifier.node, Reading::ValueType(frame)));
                let name = self.name_at(parameter.named);
                let extended = self
                    .scope
                    .extend_typed(frame, name, parameter.classifier.node);
                self.scope.mention(extended);
                frame = Frame::Inner(extended);
            }
        }
        Ok(())
    }

    /// Decode each described family the native reading does not own at its
    /// ordinary admission position.
    ///
    /// # Specification
    /// - requires: the ordinary mint sweep has lowered the written classifiers.
    /// - ensures: a decoded family's signature is pushed onto the module's list
    ///   and its index recorded by its slot; decoding failures remain located
    ///   diagnostics and refuse only their slot. Newly allocated nodes receive
    ///   provenance without replacing older origins.
    /// - fails: the existing fuel or molded-grammar refusal remains an engine
    ///   error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the lowering fuel or grammar failure encountered during the
    /// walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a codata family is refused at its own span by the
    ///   decoder while the data family beside it keeps its native signature.
    /// - witness: `description::tests::codata_is_refused_by_the_decoder_and_data_beside_it_is_native`
    #[spec(
        captures: before = self.data.len(),
        ensures: |result| result.is_err() || (self.data.len() >= before && self.described.keys().all(|position| self.collected.slots.get(usize::from(*position)).is_some())),
    )]
    pub(super) fn mint_descriptions(
        &mut self,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut types = BTreeMap::new();
        for position in 0 .. self.collected.slots.len() {
            self.fuel.spend()?;
            let Some(slot) = self.collected.slots.get(position)
            else {
                break;
            };
            let Some(entry) = self.collected.descriptions.get(&slot.introduced_by.node)
            else {
                continue;
            };
            if let Maybe::Present(_) = slot.refusal {
                continue;
            }
            if self.natively_read(entry)?.0 {
                continue;
            }
            let at = entry.at;
            let constant = slot.constant;
            types.insert(entry.description.id.name.clone(), TypeBinding::Nominal {
                declaration: constant,
                arity: TypeArity(entry.parameters.len()),
            });
            let before = sink.arena.watermark();
            let result = self.decode_family(sink.arena, entry, constant, &types);
            if let Maybe::Present(origin) = self.origin_at(at.node) {
                for id in sink.arena.values_since(before) {
                    sink.origins.record_value(id, origin);
                }
                for id in sink.arena.value_types_since(before) {
                    sink.origins.record_value_type(id, origin);
                }
            }
            match result {
                | Ok(signature) => {
                    let index = DataIndex::from(self.data.len());
                    self.data.push(Arc::new(signature));
                    let _first = self.described.insert(SlotIndex::from(position), index);
                },
                | Err(error) => {
                    self.collected
                        .description_diagnostics
                        .push(DescriptionDiagnostic {
                            span: at.span,
                            fault: DescriptionFault::NativeDecode(error),
                        });
                    if let Some(node) = self.tree.node(at.node)
                        && let Shape::Form { name, .. } = shape_of(self.pbg, node)?
                        && let Some(slot) = self.collected.slots.get_mut(position)
                    {
                        slot.refuse(at.node, LoweringRefusal::OutOfFragment {
                            span: at.span,
                            form: name,
                            sort: FragmentSort::Declaration,
                            boundary: FragmentBoundary::Unadmitted,
                        });
                    }
                },
            }
        }
        Ok(())
    }

    /// Interpret a family under every explicit parameter, with no carrier
    /// alias.
    ///
    /// # Specification
    /// - requires: `entry` and its classifier nodes belong to this lowering
    ///   run.
    /// - ensures: parameter classifiers retain prefix scope and fields retain
    ///   full telescope scope; type arguments and ordinary indices remain
    ///   distinct.
    /// - fails: missing classifiers or unsupported description leaves return a
    ///   decoder refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the exact refusal from the native description interpreter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameterised codata family reaches the decoder
    ///   under its telescope and is refused there, at the family.
    /// - witness: `description::tests::codata_is_refused_by_the_decoder_and_data_beside_it_is_native`
    #[spec(ensures: |result| result.as_ref().map_or(true, |signature| signature.parameters().len() == entry.parameters.len()))]
    fn decode_family(
        &self,
        arena: &mut CoreArena,
        entry: &DescribedDeclaration,
        constant: ConstantIndex,
        types: &BTreeMap<Name, TypeBinding>,
    ) -> Result<DataSignature, DecodeError>
    {
        let Maybe::Present(classifier) = entry.classifier
        else {
            return Err(DecodeError::MalformedCode);
        };
        let Maybe::Present(kind) = self.value_type_at(classifier.node)
        else {
            return Err(DecodeError::MalformedCode);
        };
        let parameters: Result<Vec<_>, _> = entry
            .parameters
            .iter()
            .map(
                |parameter| match self.value_type_at(parameter.classifier.node) {
                    | Maybe::Present(classifier) => Ok(classifier),
                    | Maybe::Absent(_) => Err(DecodeError::MalformedCode),
                },
            )
            .collect();
        let parameters = parameters?;
        let locals: Vec<_> = entry
            .parameters
            .iter()
            .zip(&parameters)
            .enumerate()
            .map(|(position, (parameter, &classifier))| LocalBinding {
                name: &parameter.name,
                binding: TypeBinding::Parameter {
                    level: ParameterLevel(position),
                    classifier,
                },
            })
            .collect();
        let arguments: Result<Vec<_>, _> = (0 .. parameters.len())
            .rev()
            .map(|index| {
                let index =
                    u32::try_from(index).map_err(|_overflow| DecodeError::ParameterArity)?;
                Ok(arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)))
            })
            .collect();
        let arguments = arguments?;
        let self_type = arena.value_type_data(constant, arguments);
        let context = DecodeContext {
            self_sort: NameRef::from(entry.description.id.name.as_ref()),
            self_type,
            types,
            locals: &locals,
            depth: ParameterDepth(parameters.len()),
        };
        decode_signature(arena, &entry.description, context, parameters, kind)
    }
}
