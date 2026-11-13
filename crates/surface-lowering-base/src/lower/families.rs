//! The host of the lowering's families, which one family reaches the others
//! through.
//!
//! A family in a crate of its own, over this crate, holds its host as
//! `F: Families`. So each call is static and inlines as a call of the
//! lowering's own method does.

use alloc::vec::Vec;

use gandr_core_term::ComputationId;
use gandr_core_term::hole::HoleForm;
use gandr_core_term::hole::HoleId;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Stretch;
use super::arity::Dependent;
use super::arity::Entry;
use super::arity::Planned;
use super::arity::Thunked;
use super::arity::stated_labels;
use super::context::Context;
use super::identity::Layout;
use super::identity::related;
use super::implicit::Nomination;
use super::lowered;
use super::method::unindexing;
use super::model::ModelSlot;
use super::named;
use super::native::Answer;
use super::native::answered;
use crate::error::LoweringRefusal;
use crate::form::Boxed;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Placed;
use crate::module::Constructor;
use crate::module::StructureIndex;
use crate::module::TelescopeEntry;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::Telescope;
use crate::resolve::TypeAtom;
use crate::resolve::binder_type;
use crate::resolve::type_head;

/// The host of the lowering's families.
///
/// The host holds the lowering's context and answers each call that one
/// family makes into another. The lowering implements it, and each method is
/// the lowering's own method of the same name.
pub trait Families<'run, 'source>
{
    /// The lowering's context, to read.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: gives a reference to the context that the host holds; no state
    ///   is read.
    fn context(&self) -> &Context<'run, 'source>;

    /// The lowering's context, to write.
    ///
    /// # Specification
    /// trivial.
    fn context_mut(&mut self) -> &mut Context<'run, 'source>;

    /// The domain and the answered codomain of the arrow `answer` answers, as
    /// `answered_arrow` reads them.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn arrow_of(
        &mut self,
        answer: Answer,
    ) -> Result<Option<(NodeIndex, Answer)>, LoweringRefusal<'source>>;

    /// The nullary type atom `name` spells in the source being lowered: an
    /// ambient atom, or one a listed import of its home binds, `import
    /// std.buffer (Buf);` (#4522).
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn atom(
        &self,
        name: SurfaceName<'source>,
    ) -> Maybe<TypeAtom, type_head::Absent>;

    /// The bracket of the instantiation at `site` when it reads as an element
    /// index `xs[i]`. The head of such an index is a name that a value
    /// binds.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn bare_index(
        &mut self,
        site: Site,
    ) -> Result<Maybe<ByteSpan, unindexing::Absent>, LoweringRefusal<'source>>;

    /// Read a block, `{ s… c }`, whose first statement reads under `frame`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn block(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Block, LoweringRefusal<'source>>;

    /// Whether the type written at `at` is the box, as `writes_box` reads it
    /// over this lowering's scratch buffer.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn boxes(
        &mut self,
        at: NodeIndex,
    ) -> Result<Boxed, LoweringRefusal<'source>>;

    /// Keep that the name written at `span` names `constructor`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn constructed_at(
        &mut self,
        span: ByteSpan,
        constructor: Constructor,
    );

    /// Whether each link of a type over labels binds: one answer per entry but
    /// the last, in written order, each whether a later entry names that
    /// entry's label.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn dependent_links(
        &mut self,
        typed: &[Entry<'source>],
    ) -> Result<Maybe<Vec<Dependent>, stated_labels::Absent>, LoweringRefusal<'source>>;

    /// Append the domains a value function space's domain operand writes to the
    /// operand store.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn domains(
        &mut self,
        domain: Placed,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// The name of the hole written at `at`: its form's group, and its place
    /// among the group's holes in the order the text writes them. A hole
    /// keeps its name however the text around it is spelled or laid out,
    /// and whatever another declaration writes.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn hole(
        &mut self,
        at: Placed,
    ) -> Result<HoleId, LoweringRefusal<'source>>;

    /// The group of the layout block `block`: the number a hole's name holds
    /// for the block, and the group's first block. A block that holds a
    /// top-level form joins the group of the block before it when one slot
    /// owns both forms, as a signature and its definition, or a declaration
    /// and its attributes. A block that holds a root joins the group before
    /// it, and the first block after the leading roots joins their group.
    /// Thus a tree joined after a closure numbers its groups as the parse
    /// of its whole text does. Each other block opens the next group, so a
    /// rewrite that writes a declaration in one form or in two renames no
    /// hole of another declaration (#5469).
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn hole_group(
        &mut self,
        block: LayoutBlock,
    ) -> (HoleForm, LayoutBlock);

    /// The model type the implicit `entry` of the declaration at `site` is
    /// written at, beside its slot, when it is a model implicit whose
    /// theory states a component.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn implicit_slot(
        &mut self,
        site: Site,
        entry: TelescopeEntry<'source>,
    ) -> Result<Option<(Placed, ModelSlot)>, LoweringRefusal<'source>>;

    /// The module and member a selection `head` links, when it is a selection
    /// the reading did not repair.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn linked_selection(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Option<(Placed, Placed)>, LoweringRefusal<'source>>;

    /// Mint a block: its statements bound over its last computation.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn mint_block(
        &self,
        block: Block,
        sink: &mut Sink<'_>,
    ) -> Maybe<ComputationId, lowered::Absent>;

    /// Mint `body`, the block of a function's, a lambda's or a thunk's body, a
    /// copattern clause or a handled subject, with every exit put where the
    /// body ends.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn mint_body(
        &self,
        body: Block,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>;

    /// Record that a type position at `node` names `binder`, and answer the
    /// telescope its index counts in: a type a body quotes counts in its own,
    /// leaving the signature's arrows as they are, and any other type in the
    /// signature's, whose arrow binding `binder` becomes dependent (#547).
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn name_in_type(
        &mut self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Telescope;

    /// Nominate a hole for `nomination`, an implicit a call omits, a component
    /// of the model a capability scope names none of, a wildcard or a
    /// splice the text writes: the next name of its kind in the group of
    /// the form the lowering reads now (`hole_group`).
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn nominate(
        &mut self,
        nomination: Nomination<'source>,
    ) -> Result<HoleId, LoweringRefusal<'source>>;

    /// Report the binder `binder`, spelling `name` and extending `frame`,
    /// against the outermost scope, and keep the binding it hides.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn note_binder(
        &mut self,
        binder: Placed,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// Read `body`, the block of a function's, a lambda's or a thunk's body, as
    /// one a path runs through, its last computation where the body ends.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn open_body(
        &mut self,
        site: Site,
        body: Block,
        answer: Maybe<Answer, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// Read `subject`, the block the capability scope at `site` handles, as
    /// one a path runs through on its way through the body the scope stands
    /// in.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn open_subject(
        &mut self,
        site: super::Site,
        subject: Block,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// The module the path `head` then `links` names from the declaration
    /// owning `site`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn opened_module(
        &mut self,
        site: Site,
        head: Placed,
        links: &[Placed],
    ) -> Result<StructureIndex, LoweringRefusal<'source>>;

    /// Pass the model implicit `implicit` of `function`, whose slot is `slot`,
    /// at the call `site` read under `frame`: one operand per component,
    /// the value the resident `value` supplies when it is written
    /// (`supply_model`) and a hole the call nominates otherwise, with the
    /// slot's candidates planned (`model_candidates`).
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn pass_model(
        &mut self,
        site: Site,
        frame: Frame,
        names: (SurfaceName<'source>, SurfaceName<'source>),
        slot: &ModelSlot,
        value: Option<NodeIndex>,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// Mark `inner`, standing in tail position of `outer`, with the paths
    /// through `outer`: where a path ends, where an exit may stand, where a
    /// local end continues a block, where a path through a loop's body
    /// ends, where a `break` or a `continue` may stand, where a handled
    /// subject's result is, where a handler's frame is live, the body the
    /// path runs through, and whether a statement written `c ;` holds it.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn pass_paths(
        &mut self,
        outer: NodeIndex,
        inner: NodeIndex,
    );

    /// Record `plan` for the form at `site`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn plan(
        &mut self,
        site: Site,
        plan: Plan,
    );

    /// Plan the form at `site` as `plan`, a head applied to the arguments
    /// `read` holds, each read as a value in `frame`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn plan_applied(
        &mut self,
        site: Site,
        plan: Plan,
        read: Stretch,
        frame: Frame,
    );

    /// Read `position` as `reading`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn read(
        &mut self,
        position: NodeIndex,
        reading: Reading,
    );

    /// The binder frame of a form whose position demands `produced`, with the
    /// bridge the position writes over it.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn require(
        &mut self,
        site: Site,
        produced: Produced,
    ) -> Result<Frame, LoweringRefusal<'source>>;

    /// What `name`, written at `site` under `frame`, resolves to: the innermost
    /// binder carrying it, else a declaration strictly earlier than the one
    /// `site` belongs to, another member of its mutual block, or that
    /// declaration itself when it is a data declaration, searched from that
    /// declaration's own module outward to the top level.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn resolve_name(
        &mut self,
        site: Site,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>;

    /// Keep that the name written at `span` resolved to `resolved`: a binder by
    /// its written name, a declaration by its admission position.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn resolved(
        &mut self,
        span: ByteSpan,
        resolved: Resolved,
    );

    /// The plan a name that resolved to `resolved` stands as, read as a value
    /// at `site` under `frame`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn resolved_term(
        &mut self,
        site: Site,
        frame: Frame,
        resolved: Resolved,
    ) -> Result<Plan, LoweringRefusal<'source>>;

    /// The type the scrutinee `scrutinee` of a match under `frame` was written
    /// with: its binder's or its declaration's, when it is a name, or the
    /// result its function states, when it is a call.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn scrutinee_type(
        &mut self,
        frame: Frame,
        scrutinee: Placed,
    ) -> Result<Maybe<NodeIndex, binder_type::Absent>, LoweringRefusal<'source>>;

    /// The entries of the type over labels `former` the type at `node` states,
    /// read through parentheses and, when `thunked`, one `+U`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn stated_entries(
        &mut self,
        site: Site,
        node: NodeIndex,
        former: Former,
        thunked: Thunked,
    ) -> Result<Maybe<Vec<Entry<'source>>, stated_labels::Absent>, LoweringRefusal<'source>>;

    /// The type over labels `former` the type at `node` states, read through
    /// parentheses and, when `thunked`, one `+U`: its own node and its entries.
    /// A sum chain `A + B + …` states the labelled sum `+{A, B, …}`, a
    /// product chain `A * B * …` the telescope `#{A, B, …}`, and a lazy
    /// product chain `C & D & …` the lazy record `&{C, D, …}`.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn stated_form(
        &mut self,
        site: Site,
        node: NodeIndex,
        former: Former,
        thunked: Thunked,
    ) -> Result<
        Maybe<(NodeIndex, Vec<Entry<'source>>), stated_labels::Absent>,
        LoweringRefusal<'source>,
    >;

    /// The record the type at `stated` abbreviates when it is written as an
    /// equivalence or a quasi-inverse.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn stated_relation(
        &mut self,
        stated: NodeIndex,
    ) -> Result<Maybe<Layout, related::Absent>, LoweringRefusal<'source>>;

    /// Plan the instantiation at `site` that supplies a function's implicits or
    /// stages where no call applies it: the function applied to its implicits
    /// under a lambda for each explicit parameter before the last of them,
    /// a function of the rest; or, a stage supplied, the call of the
    /// function under a lambda for each explicit parameter.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn supplied_value(
        &mut self,
        site: Site,
    ) -> Result<Planned, LoweringRefusal<'source>>;

    /// The form a selection's or a view block's target `target` writes inside
    /// any parentheses around it, `f a` of `(f a).l`, of `((f a)).l` and of
    /// `(f a) as w { … }`, its nodes owned as the selection or the view
    /// block `anchor` is.
    ///
    /// # Specification
    /// - provides: as the host's method of the same name.
    /// - fails: as the host's method of the same name.
    /// - panics: as the host's method of the same name.
    /// - executable: none — the host's method of the same name checks its
    ///   clauses.
    ///
    /// # Errors
    /// The host's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the host's method of the same name.
    /// - declaration-only: the host's method of the same name names the
    ///   witnesses.
    fn ungrouped_target(
        &mut self,
        target: Placed,
        anchor: NodeIndex,
    ) -> Result<Option<Placed>, LoweringRefusal<'source>>;
}
