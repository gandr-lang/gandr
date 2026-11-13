//! The lowering as the host of its families: it holds the context and
//! answers each call that one family makes into another, each with its own
//! method of the same name.

use alloc::vec::Vec;

use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::capability::RegionBinder;
use gandr_core_term::hole::HoleForm;
use gandr_core_term::hole::HoleId;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_lowering_base::by_form::FormStretch;
use gandr_surface_lowering_base::error::LoweringRefusal;
use gandr_surface_lowering_base::form::Boxed;
use gandr_surface_lowering_base::form::Cursor;
use gandr_surface_lowering_base::form::Former;
use gandr_surface_lowering_base::form::Placed;
use gandr_surface_lowering_base::form::TileName;
use gandr_surface_lowering_base::form::Universe;
use gandr_surface_lowering_base::lower::Block;
use gandr_surface_lowering_base::lower::Code;
use gandr_surface_lowering_base::lower::Function;
use gandr_surface_lowering_base::lower::LabelRead;
use gandr_surface_lowering_base::lower::Lowered;
use gandr_surface_lowering_base::lower::Plan;
use gandr_surface_lowering_base::lower::Produced;
use gandr_surface_lowering_base::lower::Reading;
use gandr_surface_lowering_base::lower::Resolved;
use gandr_surface_lowering_base::lower::Sink;
use gandr_surface_lowering_base::lower::Site;
use gandr_surface_lowering_base::lower::Stretch;
use gandr_surface_lowering_base::lower::arity::Dependent;
use gandr_surface_lowering_base::lower::arity::Entry;
use gandr_surface_lowering_base::lower::arity::Grouped;
use gandr_surface_lowering_base::lower::arity::Planned;
use gandr_surface_lowering_base::lower::arity::Thunked;
use gandr_surface_lowering_base::lower::arity::stated_labels;
use gandr_surface_lowering_base::lower::capability;
use gandr_surface_lowering_base::lower::context::Context;
use gandr_surface_lowering_base::lower::families::Families;
use gandr_surface_lowering_base::lower::identity::Layout;
use gandr_surface_lowering_base::lower::identity::related;
use gandr_surface_lowering_base::lower::implicit::Nomination;
use gandr_surface_lowering_base::lower::inert::Read;
use gandr_surface_lowering_base::lower::lowered;
use gandr_surface_lowering_base::lower::method::unindexing;
use gandr_surface_lowering_base::lower::model;
use gandr_surface_lowering_base::lower::model::ComponentPlace;
use gandr_surface_lowering_base::lower::model::ModelSlot;
use gandr_surface_lowering_base::lower::model::Supplied;
use gandr_surface_lowering_base::lower::named;
use gandr_surface_lowering_base::lower::native;
use gandr_surface_lowering_base::lower::native::Answer;
use gandr_surface_lowering_base::lower::native::CalledAt;
use gandr_surface_lowering_base::lower::native::Unwrapped;
use gandr_surface_lowering_base::lower::native::answered;
use gandr_surface_lowering_base::lower::native::constructed;
use gandr_surface_lowering_base::lower::native::inherited;
use gandr_surface_lowering_base::lower::native::unfolding;
use gandr_surface_lowering_base::module::Constructor;
use gandr_surface_lowering_base::module::DeclarationOutcome;
use gandr_surface_lowering_base::module::DeclarationSlot;
use gandr_surface_lowering_base::module::SlotIndex;
use gandr_surface_lowering_base::module::StructureIndex;
use gandr_surface_lowering_base::module::TelescopeEntry;
use gandr_surface_lowering_base::module::TypeComponent;
use gandr_surface_lowering_base::module::WordsForm;
use gandr_surface_lowering_base::namespace::NamePath;
use gandr_surface_lowering_base::origin::Origin;
use gandr_surface_lowering_base::resolve::Frame;
use gandr_surface_lowering_base::resolve::Mentioned;
use gandr_surface_lowering_base::resolve::ScopeId;
use gandr_surface_lowering_base::resolve::SurfaceName;
use gandr_surface_lowering_base::resolve::Telescope;
use gandr_surface_lowering_base::resolve::TypeAtom;
use gandr_surface_lowering_base::resolve::binder_type;
use gandr_surface_lowering_base::resolve::type_head;
use gandr_surface_lowering_expression::lower::Expressions;
use gandr_surface_lowering_expression::lower::ExpressionsRef;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::capability::Capability;
use super::exits::Exits;
use super::exits::ExitsRef;
use super::identity::Identities;
use super::identity::IdentitiesRef;
use super::model::Models;
use super::model::ModelsRef;
use super::native::Native;
use super::native::NativeRef;

impl<'run, 'source> Families<'run, 'source> for Lowerer<'run, 'source>
{
    /// The native family's `answered_type`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn answered_type(
        &self,
        answer: Answer,
        sink: &mut Sink<'_>,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        NativeRef::over(&self.cx).answered_type(answer, sink)
    }

    /// The model family's `answering_model`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn answering_model(
        &mut self,
        site: Site,
        theory: SurfaceName<'source>,
        slot: &ModelSlot,
    ) -> Result<Supplied, LoweringRefusal<'source>>
    {
        Models::new(self).answering_model(site, theory, slot)
    }

    /// The lowering's own `box_output`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn box_output(
        &mut self,
        codomain: Placed,
        frame: Frame,
    ) -> Result<Reading, LoweringRefusal<'source>>
    {
        Expressions::new(self).box_output(codomain, frame)
    }

    /// The lowering's own `box_returns`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn box_returns(
        &self,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        ExpressionsRef::new(self).box_returns(codomain, sink, origin)
    }

    /// The native family's `called_result`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn called_result(
        &mut self,
        site: Site,
        frame: Frame,
        call: Placed,
    ) -> Result<Option<Placed>, LoweringRefusal<'source>>
    {
        Native::new(self).called_result(site, frame, call)
    }

    /// The native family's `carry_value_type`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carry_value_type(
        &self,
        ty: ValueTypeId,
        from: Frame,
        telescope: Telescope,
        to: Frame,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        NativeRef::over(&self.cx).carry_value_type(ty, from, telescope, to, sink, origin)
    }

    /// The lowering's own `chained`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn chained(
        &mut self,
        site: Site,
        operand: NodeIndex,
        former: Former,
    ) -> Result<Option<[NodeIndex; 2]>, LoweringRefusal<'source>>
    {
        Expressions::new(self).chained(site, operand, former)
    }

    /// The lowering's own `classify_members`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn classify_members(
        &mut self,
        site: Site,
        members: Stretch,
        frame: Frame,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Expressions::new(self).classify_members(site, members, frame)
    }

    /// The native family's `constructor_named`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn constructor_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Maybe<Constructor, constructed::Absent>
    {
        Native::new(self).constructor_named(site, name)
    }

    /// The context the lowering holds, to read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn context(&self) -> &Context<'run, 'source>
    {
        &self.cx
    }

    /// The context the lowering holds, to write.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn context_mut(&mut self) -> &mut Context<'run, 'source>
    {
        &mut self.cx
    }

    /// The lowering's own `arrow_of`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arrow_of(
        &mut self,
        answer: Answer,
    ) -> Result<Option<(NodeIndex, Answer)>, LoweringRefusal<'source>>
    {
        Expressions::new(self).arrow_of(answer)
    }

    /// The lowering's own `atom`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn atom(
        &self,
        name: SurfaceName<'source>,
    ) -> Maybe<TypeAtom, type_head::Absent>
    {
        ExpressionsRef::new(self).atom(name)
    }

    /// The capability family's `bare_index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn bare_index(
        &mut self,
        site: Site,
    ) -> Result<Maybe<ByteSpan, unindexing::Absent>, LoweringRefusal<'source>>
    {
        Capability::new(self).bare_index(site)
    }

    /// The lowering's own `block`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn block(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Block, LoweringRefusal<'source>>
    {
        Expressions::new(self).block(site, cursor, frame)
    }

    /// The lowering's own `boxes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn boxes(
        &mut self,
        at: NodeIndex,
    ) -> Result<Boxed, LoweringRefusal<'source>>
    {
        Expressions::new(self).boxes(at)
    }

    /// The native family's `called_environment`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn called_environment(
        &self,
        declared: CalledAt,
        written: NodeIndex,
        sink: &Sink<'_>,
    ) -> Maybe<(ValueTypeId, Vec<ValueId>), lowered::Absent>
    {
        NativeRef::over(&self.cx).called_environment(declared, written, sink)
    }

    /// The identity family's `callee_result`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn callee_result(
        &self,
        constant: ConstantIndex,
    ) -> Option<NodeIndex>
    {
        IdentitiesRef::new(self).callee_result(constant)
    }

    /// The native family's `construct`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn construct(
        &mut self,
        site: Site,
        constructor: Constructor,
        fields: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Native::new(self).construct(site, constructor, fields)
    }

    /// The lowering's own `constructed_at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn constructed_at(
        &mut self,
        span: ByteSpan,
        constructor: Constructor,
    )
    {
        Expressions::new(self).constructed_at(span, constructor);
    }

    /// The native family's `constructor_head`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn constructor_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        Native::new(self).constructor_head(site, head)
    }

    /// The native family's `definition_written`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn definition_written(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<NodeIndex, unfolding::Absent>
    {
        NativeRef::over(&self.cx).definition_written(constant)
    }

    /// The model family's `dependent_links`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn dependent_links(
        &mut self,
        typed: &[Entry<'source>],
    ) -> Result<Maybe<Vec<Dependent>, stated_labels::Absent>, LoweringRefusal<'source>>
    {
        Models::new(self).dependent_links(typed)
    }

    /// The lowering's own `domains`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn domains(
        &mut self,
        domain: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Expressions::new(self).domains(domain)
    }

    /// The identity family's `function_of`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn function_of(
        &self,
        constant: ConstantIndex,
    ) -> Option<Function>
    {
        IdentitiesRef::new(self).function_of(constant)
    }

    /// The native family's `held_at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn held_at(
        &mut self,
        stated: NodeIndex,
    ) -> Result<native::Holds, LoweringRefusal<'source>>
    {
        Native::new(self).held_at(stated)
    }

    /// The lowering's own `hole`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole(
        &mut self,
        at: Placed,
    ) -> Result<HoleId, LoweringRefusal<'source>>
    {
        Expressions::new(self).hole(at)
    }

    /// The lowering's own `hole_group`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole_group(
        &mut self,
        block: LayoutBlock,
    ) -> (HoleForm, LayoutBlock)
    {
        Expressions::new(self).hole_group(block)
    }

    /// The lowering's own `implicit_slot`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn implicit_slot(
        &mut self,
        site: Site,
        entry: TelescopeEntry<'source>,
    ) -> Result<Option<(Placed, ModelSlot)>, LoweringRefusal<'source>>
    {
        Expressions::new(self).implicit_slot(site, entry)
    }

    /// The lowering's own `inert_read`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn inert_read(
        &self,
        site: Site,
        reached: Read<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        ExpressionsRef::new(self).inert_read(site, reached)
    }

    /// The lowering's own `inherit_owner`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn inherit_owner(
        &mut self,
        position: NodeIndex,
    )
    {
        Expressions::new(self).inherit_owner(position);
    }

    /// The lowering's own `labelled`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn labelled(
        &mut self,
        written: ByteSpan,
        held: NodeIndex,
        read: LabelRead,
    )
    {
        Expressions::new(self).labelled(written, held, read);
    }

    /// The lowering's own `linked_selection`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn linked_selection(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Option<(Placed, Placed)>, LoweringRefusal<'source>>
    {
        Expressions::new(self).linked_selection(site, head)
    }

    /// The lowering's own `located_type`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn located_type(
        &mut self,
        site: Site,
        operand: Placed,
        constant: ConstantIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Expressions::new(self).located_type(site, operand, constant)
    }

    /// The native family's `looped_point`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn looped_point(
        &mut self,
        point: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        Native::new(self).looped_point(point)
    }

    /// The lowering's own `member_definition`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn member_definition(
        &mut self,
        frame: Frame,
        at: Placed,
    ) -> Result<Option<(NodeIndex, SlotIndex)>, LoweringRefusal<'source>>
    {
        Expressions::new(self).member_definition(frame, at)
    }

    /// The lowering's own `mint_block`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn mint_block(
        &self,
        block: Block,
        sink: &mut Sink<'_>,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        ExpressionsRef::new(self).mint_block(block, sink)
    }

    /// The exits family's `mint_body`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn mint_body(
        &self,
        body: Block,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        ExitsRef::new(self).mint_body(body, sink, origin)
    }

    /// The lowering's own `mint_code`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn mint_code(
        &self,
        code: Code,
        arguments: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        ExpressionsRef::new(self).mint_code(code, arguments, sink, origin)
    }

    /// The model family's `mint_returns`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn mint_returns(
        &self,
        entries: FormStretch,
        effects: gandr_core_term::effect::EffectRow,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        ModelsRef::new(self).mint_returns(entries, effects, sink, origin)
    }

    /// The model family's `mint_supplied`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn mint_supplied(
        &self,
        supplied: &Supplied,
        place: ComponentPlace,
        under: Binders,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        ModelsRef::new(self).mint_supplied(supplied, place, under, sink, origin)
    }

    /// The lowering's own `name_in_type`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name_in_type(
        &mut self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Telescope
    {
        Expressions::new(self).name_in_type(node, binder)
    }

    /// The model family's `named_model`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn named_model(
        &mut self,
        site: Site,
        module: Placed,
        slot: &ModelSlot,
    ) -> Result<Supplied, LoweringRefusal<'source>>
    {
        Models::new(self).named_model(site, module, slot)
    }

    /// The lowering's own `names_own_binder`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn names_own_binder(
        &self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Mentioned
    {
        ExpressionsRef::new(self).names_own_binder(node, binder)
    }

    /// The lowering's own `nominate`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn nominate(
        &mut self,
        nomination: Nomination<'source>,
    ) -> Result<HoleId, LoweringRefusal<'source>>
    {
        Expressions::new(self).nominate(nomination)
    }

    /// The lowering's own `note_binder`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn note_binder(
        &mut self,
        binder: Placed,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Expressions::new(self).note_binder(binder, frame, name)
    }

    /// The exits family's `open_body`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn open_body(
        &mut self,
        site: Site,
        body: Block,
        answer: Maybe<Answer, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Exits::new(self).open_body(site, body, answer)
    }

    /// The exits family's `open_subject`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn open_subject(
        &mut self,
        site: super::Site,
        subject: Block,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Exits::new(self).open_subject(site, subject)
    }

    /// The lowering's own `opened_module`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn opened_module(
        &mut self,
        site: Site,
        head: Placed,
        links: &[Placed],
    ) -> Result<StructureIndex, LoweringRefusal<'source>>
    {
        Expressions::new(self).opened_module(site, head, links)
    }

    /// The model family's `operation_domain`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn operation_domain(
        &self,
        slot: &ModelSlot,
        place: ComponentPlace,
        sorts: &[(&Name, ValueTypeId)],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        ModelsRef::new(self).operation_domain(slot, place, sorts, sink, origin)
    }

    /// The lowering's own `outcome`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        ExpressionsRef::new(self).outcome(position, slot)
    }

    /// The lowering's own `own_written`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn own_written(
        &mut self,
        written: NodeIndex,
        anchor: NodeIndex,
    )
    {
        Expressions::new(self).own_written(written, anchor);
    }

    /// The lowering's own `parameter_export`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn parameter_export(
        &self,
        parameter: StructureIndex,
        member: SurfaceName<'source>,
    ) -> Option<SlotIndex>
    {
        ExpressionsRef::new(self).parameter_export(parameter, member)
    }

    /// The lowering's own `pass_model`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pass_model(
        &mut self,
        site: Site,
        frame: Frame,
        names: (SurfaceName<'source>, SurfaceName<'source>),
        slot: &ModelSlot,
        value: Option<NodeIndex>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Expressions::new(self).pass_model(site, frame, names, slot, value)
    }

    /// The exits family's `pass_paths`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pass_paths(
        &mut self,
        outer: NodeIndex,
        inner: NodeIndex,
    )
    {
        Exits::new(self).pass_paths(outer, inner);
    }

    /// The lowering's own `patched_at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn patched_at(
        &self,
        declared: NodeIndex,
    ) -> Result<Maybe<(), ()>, LoweringRefusal<'source>>
    {
        ExpressionsRef::new(self).patched_at(declared)
    }

    /// The lowering's own `path_head`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn path_head(
        &mut self,
        site: Site,
        target: Placed,
        links: &mut Vec<(Placed, Placed)>,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        Expressions::new(self).path_head(site, target, links)
    }

    /// The lowering's own `path_named`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn path_named(
        &self,
        head: Placed,
        links: &[(Placed, Placed)],
    ) -> NamePath
    {
        ExpressionsRef::new(self).path_named(head, links)
    }

    /// The lowering's own `phased`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn phased(
        &self,
        site: Site,
        reached: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        ExpressionsRef::new(self).phased(site, reached)
    }

    /// The lowering's own `plan`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plan(
        &mut self,
        site: Site,
        plan: Plan,
    )
    {
        Expressions::new(self).plan(site, plan);
    }

    /// The lowering's own `plan_applied`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plan_applied(
        &mut self,
        site: Site,
        plan: Plan,
        read: Stretch,
        frame: Frame,
    )
    {
        Expressions::new(self).plan_applied(site, plan, read, frame);
    }

    /// The lowering's own `plan_slot`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plan_slot(
        &mut self,
        site: Site,
        slot: &model::ModelSlot,
        holes: Vec<gandr_core_term::hole::HoleId>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Expressions::new(self).plan_slot(site, slot, holes)
    }

    /// The lowering's own `pun`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pun(
        &mut self,
        label: Placed,
        frame: Frame,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Expressions::new(self).pun(label, frame)
    }

    /// The lowering's own `read`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn read(
        &mut self,
        position: NodeIndex,
        reading: Reading,
    )
    {
        Expressions::new(self).read(position, reading);
    }

    /// The lowering's own `region_binder`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn region_binder(
        &self,
        at: NodeIndex,
        name: SurfaceName<'source>,
    ) -> Option<RegionBinder>
    {
        ExpressionsRef::new(self).region_binder(at, name)
    }

    /// The native family's `relocate`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn relocate(
        &self,
        arena: &mut CoreArena,
        ty: CompTypeId,
        from: Frame,
        telescope: Telescope,
        lift: Binders,
        copies: Option<&mut Vec<Carried>>,
    ) -> CompTypeId
    {
        NativeRef::over(&self.cx).relocate(arena, ty, from, telescope, lift, copies)
    }

    /// The native family's `relocate_value_type`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn relocate_value_type(
        &self,
        ty: ValueTypeId,
        frame: Frame,
        telescope: Telescope,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        NativeRef::over(&self.cx).relocate_value_type(ty, frame, telescope, sink, origin)
    }

    /// The lowering's own `require`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn require(
        &mut self,
        site: Site,
        produced: Produced,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        Expressions::new(self).require(site, produced)
    }

    /// The lowering's own `resident`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn resident<Count>(
        &self,
        site: Site,
        resident: Placed,
    ) -> Result<Count, LoweringRefusal<'source>>
    where
        Count: From<usize> + PartialEq,
    {
        ExpressionsRef::new(self).resident(site, resident)
    }

    /// The lowering's own `resolve_name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn resolve_name(
        &mut self,
        site: Site,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        Expressions::new(self).resolve_name(site, frame, name)
    }

    /// The lowering's own `resolved`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn resolved(
        &mut self,
        span: ByteSpan,
        resolved: Resolved,
    )
    {
        Expressions::new(self).resolved(span, resolved);
    }

    /// The lowering's own `resolved_term`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn resolved_term(
        &mut self,
        site: Site,
        frame: Frame,
        resolved: Resolved,
    ) -> Result<Plan, LoweringRefusal<'source>>
    {
        Expressions::new(self).resolved_term(site, frame, resolved)
    }

    /// The model family's `scrutinee_type`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn scrutinee_type(
        &mut self,
        frame: Frame,
        scrutinee: Placed,
    ) -> Result<Maybe<NodeIndex, binder_type::Absent>, LoweringRefusal<'source>>
    {
        Models::new(self).scrutinee_type(frame, scrutinee)
    }

    /// The capability family's `session_type`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn session_type(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        Capability::new(self).session_type(site)
    }

    /// The lowering's own `spread`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn spread(
        &self,
        kept: FormStretch,
    ) -> Stretch
    {
        ExpressionsRef::new(self).spread(kept)
    }

    /// The model family's `stated_entries`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stated_entries(
        &mut self,
        site: Site,
        node: NodeIndex,
        former: Former,
        thunked: Thunked,
    ) -> Result<Maybe<Vec<Entry<'source>>, stated_labels::Absent>, LoweringRefusal<'source>>
    {
        Models::new(self).stated_entries(site, node, former, thunked)
    }

    /// The model family's `stated_form`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stated_form(
        &mut self,
        site: Site,
        node: NodeIndex,
        former: Former,
        thunked: Thunked,
    ) -> Result<
        Maybe<(NodeIndex, Vec<Entry<'source>>), stated_labels::Absent>,
        LoweringRefusal<'source>,
    >
    {
        Models::new(self).stated_form(site, node, former, thunked)
    }

    /// The lowering's own `stated_named`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stated_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<TypeComponent<'source>, named::Absent>, LoweringRefusal<'source>>
    {
        Expressions::new(self).stated_named(site, name)
    }

    /// The identity family's `stated_relation`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stated_relation(
        &mut self,
        stated: NodeIndex,
    ) -> Result<Maybe<Layout, related::Absent>, LoweringRefusal<'source>>
    {
        Identities::new(self).stated_relation(stated)
    }

    /// The lowering's own `stated_value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stated_value(
        &mut self,
        site: Site,
    ) -> Result<(Option<NodeIndex>, Option<native::Answer>), LoweringRefusal<'source>>
    {
        Expressions::new(self).stated_value(site)
    }

    /// The model family's `supplied_carrier`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn supplied_carrier(
        &self,
        slot: &ModelSlot,
        supplied: &Supplied,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<(Name, ValueTypeId), lowered::Absent>
    {
        ModelsRef::new(self).supplied_carrier(slot, supplied, sink, origin)
    }

    /// The lowering's own `supplied_or_refused`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn supplied_or_refused(
        &self,
        site: Site,
        constant: ConstantIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        ExpressionsRef::new(self).supplied_or_refused(site, constant)
    }

    /// The lowering's own `supplied_value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn supplied_value(
        &mut self,
        site: Site,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        Expressions::new(self).supplied_value(site)
    }

    /// The lowering's own `telescope_at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn telescope_at(
        &self,
        node: NodeIndex,
    ) -> Telescope
    {
        ExpressionsRef::new(self).telescope_at(node)
    }

    /// The model family's `theory_slot`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn theory_slot(
        &mut self,
        named: Site,
        theory: &crate::form::WrittenPath,
        at: ByteOffset,
        sorts: &[(Placed, Placed)],
    ) -> Result<ModelSlot, LoweringRefusal<'source>>
    {
        Models::new(self).theory_slot(named, theory, at, sorts)
    }

    /// The model family's `type_entries`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn type_entries(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
        closer: TileName,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        ModelsRef::new(self).type_entries(site, cursor, closer)
    }

    /// The model family's `ungrouped_target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn ungrouped_target(
        &mut self,
        target: Placed,
        anchor: NodeIndex,
    ) -> Result<Option<Placed>, LoweringRefusal<'source>>
    {
        Models::new(self).ungrouped_target(target, anchor)
    }

    /// The lowering's own `universe_tiles`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn universe_tiles(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        ExpressionsRef::new(self).universe_tiles(site, cursor)
    }

    /// The native family's `unwrapped`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn unwrapped(
        &mut self,
        node: NodeIndex,
    ) -> Result<Maybe<Unwrapped, inherited::Absent>, LoweringRefusal<'source>>
    {
        Native::new(self).unwrapped(node)
    }

    /// The native family's `words_point`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn words_point(
        &self,
        arena: &mut CoreArena,
        words: &WordsForm,
    ) -> Maybe<(ValueTypeId, ValueId), lowered::Absent>
    {
        NativeRef::over(&self.cx).words_point(arena, words)
    }

    /// The model family's `written_group`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn written_group(
        &mut self,
        at: Placed,
        frame: Frame,
    ) -> Result<Grouped, LoweringRefusal<'source>>
    {
        Models::new(self).written_group(at, frame)
    }

    /// The lowering's own `written_stack`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn written_stack(
        &mut self,
        at: NodeIndex,
    ) -> Result<capability::Stated, LoweringRefusal<'source>>
    {
        Expressions::new(self).written_stack(at)
    }

    /// The native family's `written_telescope`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn written_telescope(
        &mut self,
        node: NodeIndex,
    ) -> Result<Option<NodeIndex>, LoweringRefusal<'source>>
    {
        Native::new(self).written_telescope(node)
    }
}
