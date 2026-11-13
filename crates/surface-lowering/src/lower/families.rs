//! The lowering as the host of its families: it holds the context and
//! answers each call that one family makes into another, each with its own
//! method of the same name.

use alloc::vec::Vec;

use gandr_core_term::hole::HoleForm;
use gandr_core_term::hole::HoleId;
use gandr_surface_lowering_base::error::LoweringRefusal;
use gandr_surface_lowering_base::form::Boxed;
use gandr_surface_lowering_base::form::Former;
use gandr_surface_lowering_base::form::Placed;
use gandr_surface_lowering_base::lower::Block;
use gandr_surface_lowering_base::lower::Plan;
use gandr_surface_lowering_base::lower::Produced;
use gandr_surface_lowering_base::lower::Reading;
use gandr_surface_lowering_base::lower::Resolved;
use gandr_surface_lowering_base::lower::Site;
use gandr_surface_lowering_base::lower::Stretch;
use gandr_surface_lowering_base::lower::arity::Dependent;
use gandr_surface_lowering_base::lower::arity::Entry;
use gandr_surface_lowering_base::lower::arity::Planned;
use gandr_surface_lowering_base::lower::arity::Thunked;
use gandr_surface_lowering_base::lower::arity::stated_labels;
use gandr_surface_lowering_base::lower::context::Context;
use gandr_surface_lowering_base::lower::families::Families;
use gandr_surface_lowering_base::lower::identity::Layout;
use gandr_surface_lowering_base::lower::identity::related;
use gandr_surface_lowering_base::lower::implicit::Nomination;
use gandr_surface_lowering_base::lower::method::unindexing;
use gandr_surface_lowering_base::lower::model::ModelSlot;
use gandr_surface_lowering_base::lower::named;
use gandr_surface_lowering_base::lower::native::Answer;
use gandr_surface_lowering_base::lower::native::answered;
use gandr_surface_lowering_base::module::Constructor;
use gandr_surface_lowering_base::module::StructureIndex;
use gandr_surface_lowering_base::module::TelescopeEntry;
use gandr_surface_lowering_base::resolve::Frame;
use gandr_surface_lowering_base::resolve::ScopeId;
use gandr_surface_lowering_base::resolve::SurfaceName;
use gandr_surface_lowering_base::resolve::Telescope;
use gandr_surface_lowering_base::resolve::TypeAtom;
use gandr_surface_lowering_base::resolve::binder_type;
use gandr_surface_lowering_base::resolve::type_head;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Lowerer;

impl<'run, 'source> Families<'run, 'source> for Lowerer<'run, 'source>
{
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
        Lowerer::arrow_of(self, answer)
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
        Lowerer::atom(self, name)
    }

    /// The lowering's own `bare_index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn bare_index(
        &mut self,
        site: Site,
    ) -> Result<Maybe<ByteSpan, unindexing::Absent>, LoweringRefusal<'source>>
    {
        Lowerer::bare_index(self, site)
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
        Lowerer::boxes(self, at)
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
        Lowerer::constructed_at(self, span, constructor);
    }

    /// The lowering's own `dependent_links`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn dependent_links(
        &mut self,
        typed: &[Entry<'source>],
    ) -> Result<Maybe<Vec<Dependent>, stated_labels::Absent>, LoweringRefusal<'source>>
    {
        Lowerer::dependent_links(self, typed)
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
        Lowerer::domains(self, domain)
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
        Lowerer::hole(self, at)
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
        Lowerer::hole_group(self, block)
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
        Lowerer::implicit_slot(self, site, entry)
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
        Lowerer::linked_selection(self, site, head)
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
        Lowerer::name_in_type(self, node, binder)
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
        Lowerer::nominate(self, nomination)
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
        Lowerer::note_binder(self, binder, frame, name)
    }

    /// The lowering's own `open_body`.
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
        Lowerer::open_body(self, site, body, answer)
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
        Lowerer::opened_module(self, site, head, links)
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
        Lowerer::pass_model(self, site, frame, names, slot, value)
    }

    /// The lowering's own `pass_paths`.
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
        Lowerer::pass_paths(self, outer, inner);
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
        Lowerer::plan(self, site, plan);
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
        Lowerer::plan_applied(self, site, plan, read, frame);
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
        Lowerer::read(self, position, reading);
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
        Lowerer::require(self, site, produced)
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
        Lowerer::resolve_name(self, site, frame, name)
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
        Lowerer::resolved(self, span, resolved);
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
        Lowerer::resolved_term(self, site, frame, resolved)
    }

    /// The lowering's own `scrutinee_type`.
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
        Lowerer::scrutinee_type(self, frame, scrutinee)
    }

    /// The lowering's own `stated_entries`.
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
        Lowerer::stated_entries(self, site, node, former, thunked)
    }

    /// The lowering's own `stated_form`.
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
        Lowerer::stated_form(self, site, node, former, thunked)
    }

    /// The lowering's own `stated_relation`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stated_relation(
        &mut self,
        stated: NodeIndex,
    ) -> Result<Maybe<Layout, related::Absent>, LoweringRefusal<'source>>
    {
        Lowerer::stated_relation(self, stated)
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
        Lowerer::supplied_value(self, site)
    }

    /// The lowering's own `ungrouped_target`.
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
        Lowerer::ungrouped_target(self, target, anchor)
    }
}
