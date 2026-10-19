//! Described families the native data reading does not own, decoded from the
//! same descriptions exposed to cell consumers, and the presentation code
//! `Theory` with the values `theory` blocks define.
//!
//! A data declaration form has one producer of its signature: the native
//! reading, which also enters its constructors and compiles its matches. Its
//! description is checked and elaborated to cells beside it. Every other
//! described family — codata today — reaches the decoder here, whose refusal
//! is reported at the family. Reversal: a description decode that agrees with
//! the native reading on every data form can replace it as the producer.
//!
//! `Theory` reaches the same decoder from [`theory_desc`], and a `theory`
//! block's definition is its presentation's value read node for node: each
//! constructor of the value a constructor of `Theory`, each name a `String`
//! literal, so the core term and the identity bytes are one value in two
//! encodings.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::description::DecodeContext;
use gandr_core_term::description::DecodeError;
use gandr_core_term::description::LocalBinding;
use gandr_core_term::description::ParameterDepth;
use gandr_core_term::description::ParameterLevel;
use gandr_core_term::description::TypeArity;
use gandr_core_term::description::TypeBinding;
use gandr_core_term::description::decode_signature;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::ConstructorTag;
use gandr_theory_levitation::DescValue;
use gandr_theory_levitation::LeafBytes;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::PayloadNode;
use gandr_theory_levitation::PayloadView;
use gandr_theory_levitation::TheoryFault;
use gandr_theory_levitation::theory_desc;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Reading;
use super::Sink;
use super::Universe;
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
use crate::module::Half;
use crate::module::Operand;
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
        let (source_of, current) = (&self.source_of, self.current.source);
        for entry in self
            .collected
            .descriptions
            .values()
            .filter(|entry| source_of.get(usize::from(entry.at.node)) == Some(&current))
        {
            if self.natively_read(entry)?.0 {
                continue;
            }
            let mut frame = Frame::Outermost;
            for parameter in &entry.parameters {
                seeds.push((parameter.classifier.node, Reading::ValueType(frame)));
                let name = self.name_at(parameter.named);
                let extended = self.scope.extend_typed(
                    frame,
                    name,
                    parameter.classifier.node,
                    Maybe::Present(parameter.named.span),
                );
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
    ///   diagnostics and refuse only their slot; a `theory` block or a
    ///   top-level `oper`, which declares no family, is left alone. Newly
    ///   allocated nodes receive provenance without replacing older origins.
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every collected slot; the check reads the slot of each described position once"
        )
    )]
    #[spec(
        captures: before = self.data.len(),
        ensures: |result| result.is_err() || (self.data.len() >= before && self.described.keys().all(|position| self.collected.slots.get(usize::from(*position)).is_some())),
    )]
    pub(super) fn mint_descriptions(
        &mut self,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut types = core::mem::take(&mut self.described_types);
        for position in self.current.slots .. self.collected.slots.len() {
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
            if let Maybe::Absent(_) = entry.classifier {
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
                Ok(signature) => {
                    let index = DataIndex::from(self.data.len());
                    self.constructors.push(
                        entry
                            .description
                            .ctors
                            .iter()
                            .map(|constructor| String::from(constructor.name.as_ref()))
                            .collect(),
                    );
                    self.data.push(Arc::new(signature));
                    let _first = self.described.insert(SlotIndex::from(position), index);
                },
                Err(error) => {
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
        self.described_types = types;
        Ok(())
    }

    /// Mint `Theory` from its description, then each `theory` block's
    /// definition from the value its presentation holds.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: when the module holds `Theory`, its signature decoded from
    ///   [`theory_desc`] — no parameters, `Type` at the fuss-free level — is
    ///   pushed onto the module's list with its constructors' names and
    ///   recorded by its slot; then every unrefused slot a `theory` block
    ///   defines takes the type `Theory` and the constructor tree
    ///   [`presentation_term`] reads off its value. A value the walk refuses
    ///   refuses its slot at the block. Every node minted takes the origin of
    ///   the code's slot or the block.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk over the
    ///   slots exhausts the allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clean theory's definition is read back out of the
    ///   arena as the constructor tree its value encodes, and a program
    ///   matching on it counts its operations.
    /// - witness: `description::theory::tests::a_theory_block_defines_its_presentation`
    #[spec(
        captures: before = (self.data.len(), self.presented.len()),
        ensures: |result| result.is_err() || (self.data.len() >= before.0 && self.presented.len() >= before.1),
    )]
    pub(super) fn mint_presentations(
        &mut self,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(ref theory) = self.collected.theory
        else {
            return Ok(());
        };
        let code = theory.slot;
        let Some(slot) = self.collected.slots.get(usize::from(code))
        else {
            return Ok(());
        };
        let constant = slot.constant;
        let at = slot.introduced_by;
        if self.owns_slot(code).0 {
            let description = theory_desc(());
            let before = sink.arena.watermark();
            let kind = sink.arena.value_type_universe(
                Sort::Ground(GroundSort::Value),
                Level::constant(Universe::FUSS_FREE.level),
            );
            let self_type = sink.arena.value_type_data(constant, Vec::new());
            let types = BTreeMap::new();
            let context = DecodeContext {
                self_sort: NameRef::from(description.id.name.as_ref()),
                self_type,
                types: &types,
                locals: &[],
                depth: ParameterDepth(0),
            };
            let decoded = decode_signature(sink.arena, &description, context, Vec::new(), kind);
            self.record_since(sink, before, at.node);
            let Ok(signature) = decoded
            else {
                return Ok(());
            };
            let index = DataIndex::from(self.data.len());
            self.constructors.push(
                description
                    .ctors
                    .iter()
                    .map(|constructor| String::from(constructor.name.as_ref()))
                    .collect(),
            );
            self.data.push(Arc::new(signature));
            let _first = self.described.insert(code, index);
        }
        else if !self.described.contains_key(&code) {
            // `Theory` did not decode in the source that declares it.
            return Ok(());
        }
        for position in self.current.slots .. self.collected.slots.len() {
            self.fuel.spend()?;
            let Some(slot) = self.collected.slots.get(position)
            else {
                break;
            };
            let defines = matches!(
                slot.definition,
                Maybe::Present(Half {
                    operand: Operand::Presented,
                    ..
                })
            );
            if !defines || matches!(slot.refusal, Maybe::Present(_)) {
                continue;
            }
            let block = slot.introduced_by;
            let Some(entry) = self.collected.descriptions.get(&block.node)
            else {
                continue;
            };
            let Maybe::Present(ref presentation) = entry.presentation
            else {
                continue;
            };
            let before = sink.arena.watermark();
            let declared = sink.arena.value_type_data(constant, Vec::new());
            let body = presentation_term(sink.arena, presentation.value.as_value(), declared);
            self.record_since(sink, before, block.node);
            match body {
                Ok(body) => {
                    let _first = self
                        .presented
                        .insert(SlotIndex::from(position), (declared, body));
                },
                Err(_fault) => {
                    if let Some(node) = self.tree.node(block.node)
                        && let Shape::Form { name, .. } = shape_of(self.pbg, node)?
                        && let Some(slot) = self.collected.slots.get_mut(position)
                    {
                        slot.refuse(block.node, LoweringRefusal::OutOfFragment {
                            span: block.span,
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

    /// Record the origin of the form at `node` on every value and value type
    /// minted since `before`.
    ///
    /// # Specification
    /// - requires: `before` is a watermark of `sink`'s arena.
    /// - ensures: each node minted since `before` takes the form's origin when
    ///   the form has one; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the origin table records without exposing what it
    ///   held before.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_presentations`].
    /// - witness: `description::theory::tests::a_theory_block_defines_its_presentation`
    fn record_since(
        &self,
        sink: &mut Sink<'_>,
        before: gandr_core_term::ArenaWatermark,
        node: NodeIndex,
    )
    {
        let Maybe::Present(origin) = self.origin_at(node)
        else {
            return;
        };
        for id in sink.arena.values_since(before) {
            sink.origins.record_value(id, origin);
        }
        for id in sink.arena.value_types_since(before) {
            sink.origins.record_value_type(id, origin);
        }
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
                    Maybe::Present(classifier) => Ok(classifier),
                    Maybe::Absent(_) => Err(DecodeError::MalformedCode),
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

/// One step of [`presentation_term`]'s walk.
enum Step<'value>
{
    /// Read a constructor of the value and its payload.
    Visit(ConstructorTag, PayloadNode<'value>),
    /// Mint a name.
    Text(&'value LeafBytes),
    /// Mint a constructor over the last `fields` values minted.
    Build(ConstructorTag, usize),
}

/// The core term of `value`, a value of the description of `Theory`, each node
/// of it a constructor of `datatype`.
///
/// # Specification
/// - requires: `datatype` is the nominal type `Theory`.
/// - ensures: one constructor per constructor of `value`, at its tag, over its
///   fields in payload order — each name field a `String` literal of the name's
///   text, each recursive field the term of its value.
/// - fails: [`TheoryFault::Payload`] for a payload that is not a product of
///   names and recursions; [`TheoryFault::Text`] for a name that is not UTF-8.
/// - panics: none.
/// - intension: an explicit worklist; a visit pushes the constructor's build
///   step and then its fields, so each field's term is complete before the next
///   begins and a build pops exactly its own fields.
///
/// # Errors
/// [`TheoryFault::Payload`] and [`TheoryFault::Text`].
///
/// # Adequacy
/// - hypothesis: L3 — a presentation of one sort, one operation and one rule
///   reads back as the constructor tree its value encodes, names and tags
///   included.
/// - witness: `description::theory::tests::a_theory_block_defines_its_presentation`
#[spec(ensures: |result| result.is_ok() || matches!(result, Err(TheoryFault::Payload | TheoryFault::Text)))]
fn presentation_term(
    arena: &mut CoreArena,
    value: &DescValue,
    datatype: ValueTypeId,
) -> Result<ValueId, TheoryFault>
{
    let mut steps = vec![Step::Visit(value.ctor, value.payload.to_node())];
    let mut built: Vec<ValueId> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(tag, payload) => {
                let mut fields = Vec::new();
                let mut pending = vec![payload];
                while let Some(node) = pending.pop() {
                    match node.view() {
                        PayloadView::Unit => {},
                        PayloadView::Pair(parts) => {
                            let first = pending.len();
                            pending.extend(parts);
                            if let Some(pushed) = pending.get_mut(first ..) {
                                pushed.reverse();
                            }
                        },
                        PayloadView::Rec { ctor, mut payload } => {
                            let Some(inner) = payload.next()
                            else {
                                return Err(TheoryFault::Payload);
                            };
                            fields.push(Step::Visit(ctor, inner));
                        },
                        PayloadView::Leaf(bytes) => fields.push(Step::Text(bytes)),
                        PayloadView::Inj { .. } | PayloadView::Abs { .. } => {
                            return Err(TheoryFault::Payload);
                        },
                    }
                }
                steps.push(Step::Build(tag, fields.len()));
                steps.extend(fields.into_iter().rev());
            },
            Step::Text(bytes) => {
                let Ok(text) = core::str::from_utf8(bytes.as_ref())
                else {
                    return Err(TheoryFault::Text);
                };
                built.push(
                    arena.value_literal(Literal::Text(StringLiteral::new(String::from(text)))),
                );
            },
            Step::Build(tag, count) => {
                let fields = built.split_off(built.len().saturating_sub(count));
                built.push(arena.value_constructor(
                    datatype,
                    gandr_kernel_term::ConstructorTag::from(usize::from(tag)),
                    fields,
                ));
            },
        }
    }
    built.pop().ok_or(TheoryFault::Payload)
}
