//! The host of the lowering's families, which one family reaches the others
//! through.
//!
//! A family in a crate of its own, over this crate, holds its host as
//! `F: Families`. So each call is static and inlines as a call of the
//! lowering's own method does.

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
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Code;
use super::Function;
use super::LabelRead;
use super::Lowered;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Stretch;
use super::arity::Dependent;
use super::arity::Entry;
use super::arity::Grouped;
use super::arity::Planned;
use super::arity::Thunked;
use super::arity::stated_labels;
use super::capability;
use super::context::Context;
use super::identity::Layout;
use super::identity::related;
use super::implicit::Nomination;
use super::inert::Read;
use super::lowered;
use super::method::unindexing;
use super::model;
use super::model::ComponentPlace;
use super::model::ModelSlot;
use super::model::Supplied;
use super::named;
use super::native;
use super::native::Answer;
use super::native::CalledAt;
use super::native::Unwrapped;
use super::native::answered;
use super::native::constructed;
use super::native::inherited;
use super::native::unfolding;
use crate::by_form::FormStretch;
use crate::error::LoweringRefusal;
use crate::form::Boxed;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::Universe;
use crate::module::Constructor;
use crate::module::DeclarationOutcome;
use crate::module::DeclarationSlot;
use crate::module::SlotIndex;
use crate::module::StructureIndex;
use crate::module::TelescopeEntry;
use crate::module::TypeComponent;
use crate::module::WordsForm;
use crate::namespace::NamePath;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::Mentioned;
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
    /// The computation type `answer` states, read under its own frame: the
    /// written computation type, the returner over a written value type the
    /// position returns, or the arrows an alias stands for past the domains
    /// taken.
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
    fn answered_type(
        &self,
        answer: Answer,
        sink: &mut Sink<'_>,
    ) -> Maybe<CompTypeId, lowered::Absent>;

    /// The model answering the capability scope at `site` over `theory`,
    /// which names none: one hole per component of `slot`, each nominated as
    /// the scope's, the slot planned at the scope with every module of the
    /// theory in scope (`Self::plan_slot`).
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
    fn answering_model(
        &mut self,
        site: Site,
        theory: SurfaceName<'source>,
        slot: &ModelSlot,
    ) -> Result<Supplied, LoweringRefusal<'source>>;

    /// How a box reads its output `codomain` under `frame`: a group of
    /// outputs, `(q : A, r : B)` or `()`, and a row before a type, `[E] B`, as
    /// a definition's result is read; any other output as a value type, the
    /// returner inserted when the box is minted.
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
    fn box_output(
        &mut self,
        codomain: Placed,
        frame: Frame,
    ) -> Result<Reading, LoweringRefusal<'source>>;

    /// The computation type a box returns, its output `codomain` minted: the
    /// returner of a value type, and a group or a rowed returner as it stands.
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
    fn box_returns(
        &self,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<CompTypeId, lowered::Absent>;

    /// The result type the declaration a call names writes after its
    /// parameter list.
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
    fn called_result(
        &mut self,
        site: Site,
        frame: Frame,
        call: Placed,
    ) -> Result<Option<Placed>, LoweringRefusal<'source>>;

    /// `ty`, a value type read under `from` in `telescope`, carried into the
    /// term context of `to`, a frame whose chain passes through `from`.
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
    fn carry_value_type(
        &self,
        ty: ValueTypeId,
        from: Frame,
        telescope: Telescope,
        to: Frame,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId;

    /// The two operands of `operand` when it is an unparenthesized form of
    /// `former`, a link of the chain a form of `former` heads.
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
    fn chained(
        &mut self,
        site: Site,
        operand: NodeIndex,
        former: Former,
    ) -> Result<Option<[NodeIndex; 2]>, LoweringRefusal<'source>>;

    /// Give each member of the eager product at `site` the component its
    /// stated product writes at the member's place.
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
    fn classify_members(
        &mut self,
        site: Site,
        members: Stretch,
        frame: Frame,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// The constructor `name`, written at `site`, names: one of a data family
    /// admitted strictly before the declaration `site` belongs to, declared
    /// in `site`'s own source or, when that declares none, in one source it
    /// imports unqualified. A data family's argument at a place the family
    /// declares a universe names no constructor: no constructor is a value of
    /// a universe, so the name there is a type's. A family a module body
    /// declares lends its bare constructors only to declarations inside that
    /// module; outside it, `M.B` names them. A name that more than one family
    /// the site sees declares names none of them bare.
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
    fn constructor_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Maybe<Constructor, constructed::Absent>;

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

    /// The type written at `written`, read under the parameters before the one
    /// `declared` names, beside the arguments the call writes for the
    /// parameters it names.
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
    fn called_environment(
        &self,
        declared: CalledAt,
        written: NodeIndex,
        sink: &Sink<'_>,
    ) -> Maybe<(ValueTypeId, Vec<ValueId>), lowered::Absent>;

    /// The node a call of the declaration at `constant` reads its result off.
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
    fn callee_result(
        &self,
        constant: ConstantIndex,
    ) -> Option<NodeIndex>;

    /// Classify `constructor` applied to the fields `fields` holds in the
    /// operand store, written at `site`.
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
    fn construct(
        &mut self,
        site: Site,
        constructor: Constructor,
        fields: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>;

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

    /// The constructor `head`, the head of a call written at `site`, names.
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
    fn constructor_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>;

    /// The node of the body a top-level definition of `constant` writes: the
    /// one form of `= e ;`, or the declaration form of a function tail
    /// `(params) -> T { … }`, which the tail lowers at (#3665).
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
    fn definition_written(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<NodeIndex, unfolding::Absent>;

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

    /// The function tail the declaration at `constant` is written with, by its
    /// signature or its definition.
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
    fn function_of(
        &self,
        constant: ConstantIndex,
    ) -> Option<Function>;

    /// What a place inside a type whose written type is `stated` holds: a
    /// code when that type is a universe, and a value of it otherwise.
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
    fn held_at(
        &mut self,
        stated: NodeIndex,
    ) -> Result<native::Holds, LoweringRefusal<'source>>;

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

    /// Refuse the read, at `site`, of `reached` when it is inert and the
    /// declaration `site` belongs to is not.
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
    fn inert_read(
        &self,
        site: Site,
        reached: Read<'source>,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// Give every unowned child of `position` the declaration its parent
    /// belongs to.
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
    fn inherit_owner(
        &mut self,
        position: NodeIndex,
    );

    /// Keep the label written at `written` against the entry at `held`, read
    /// as `read`, for `record_labels`.
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
    fn labelled(
        &mut self,
        written: ByteSpan,
        held: NodeIndex,
        read: LabelRead,
    );

    /// Push onto `links` the link from `target` to `selected` through the
    /// module names `modules` passes, as [`Context::type_link`] reads them,
    /// from the outermost: the type selected from the last module, then
    /// each module from the one before it, the first from the operand.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn linked(
        links: &mut Vec<(Placed, Placed)>,
        target: Placed,
        modules: &[Piece],
        selected: Placed,
    )
    {
        let named = modules.iter().rev().filter_map(|piece| match *piece {
            Piece::Tile {
                label: TileName::TYPE_VARIABLE,
                at,
            } => Some(at),
            Piece::Tile { .. } | Piece::Operand(_) => None,
        });
        let mut selected = selected;
        for module in named {
            links.push((module, selected));
            selected = module;
        }
        links.push((target, selected));
    }

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

    /// Classify the handle type `T at w`, `w` resolved to the declaration at
    /// `constant`.
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
    fn located_type(
        &mut self,
        site: Site,
        operand: Placed,
        constant: ConstantIndex,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// The empty word `Path.here(point)` is, when `point` spells the point a
    /// family's loops are at, inside as many `Path.here` calls as the loops'
    /// point is wrapped in.
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
    fn looped_point(
        &mut self,
        point: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>;

    /// The definition the manifest type member named at `at` writes, with
    /// that member's held slot, when `at`, read under `frame`, is a type name
    /// that names one.
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
    fn member_definition(
        &mut self,
        frame: Frame,
        at: Placed,
    ) -> Result<Option<(NodeIndex, SlotIndex)>, LoweringRefusal<'source>>;

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

    /// Mint a code: its head, applied statically to the arguments `arguments`
    /// names in the operand store, left to right.
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
    fn mint_code(
        &self,
        code: Code,
        arguments: FormStretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>;

    /// Mint a function's group of outputs: the many-value returner of its
    /// entries' types, each under the entries before it, at the row
    /// `effects`.
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
    fn mint_returns(
        &self,
        entries: FormStretch,
        effects: gandr_core_term::effect::EffectRow,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>;

    /// Mint the value `supplied` passes for the component at `place` of its
    /// slot, raised past `under` binders a standing supply opens.
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
    fn mint_supplied(
        &self,
        supplied: &Supplied,
        place: ComponentPlace,
        under: Binders,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>;

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

    /// What the module whose name `module` writes in `site` passes for the
    /// slot `slot`.
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
    fn named_model(
        &mut self,
        site: Site,
        module: Placed,
        slot: &ModelSlot,
    ) -> Result<Supplied, LoweringRefusal<'source>>;

    /// Whether the type at `node`, which introduces `binder`, names it: in the
    /// telescope [`Self::name_in_type`] counted the type's reads in, so a type
    /// a body quotes depends on a binder its own reads name, and any other
    /// type on one a signature type names (#583).
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
    fn names_own_binder(
        &self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Mentioned;

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

    /// The type of the operation at `place` of the slot `slot`, each sort it
    /// reads stated by `sorts`, a sort's name beside its type.
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
    fn operation_domain(
        &self,
        slot: &ModelSlot,
        place: ComponentPlace,
        sorts: &[(&Name, ValueTypeId)],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>;

    /// What the slot at `position` amounts to in the lowered module.
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
    fn outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>;

    /// Give every unowned node written at `written` the declaration `anchor`
    /// belongs to, ahead of the walk.
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
    fn own_written(
        &mut self,
        written: NodeIndex,
        anchor: NodeIndex,
    );

    /// The value component the parameter at `parameter` states under `member`.
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
    fn parameter_export(
        &self,
        parameter: StructureIndex,
        member: SurfaceName<'source>,
    ) -> Option<SlotIndex>;

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

    /// Present when `declared`, the type a name's binder or declaration is
    /// written with, is a patched type: a staged type whose bracket writes a
    /// field form or a face form.
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
    fn patched_at(
        &self,
        declared: NodeIndex,
    ) -> Result<Maybe<(), ()>, LoweringRefusal<'source>>;

    /// The head of the chain of type paths whose innermost operand is
    /// `target`, each link it walks pushed onto `links`, from the outermost.
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
    fn path_head(
        &mut self,
        site: Site,
        target: Placed,
        links: &mut Vec<(Placed, Placed)>,
    ) -> Result<Placed, LoweringRefusal<'source>>;

    /// The name path the head `head` and the links `links` spell, from the
    /// head, as `Self::path_head` collects them.
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
    fn path_named(
        &self,
        head: Placed,
        links: &[(Placed, Placed)],
    ) -> NamePath;

    /// Refuse the read, at `site`, of the member `reached` when it stands
    /// above the phase of the member `site` belongs to.
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
    fn phased(
        &self,
        site: Site,
        reached: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>;

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

    /// Plan the model slot `slot` left to the models in scope at `site`, its
    /// components the nominated `holes`: each hole kept with the names of the
    /// slot's candidates, and the slot planned at `site` under the declaration
    /// holding it.
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
    fn plan_slot(
        &mut self,
        site: Site,
        slot: &model::ModelSlot,
        holes: Vec<gandr_core_term::hole::HoleId>,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// Plan the label tile `label` of a punned entry, `.l` in a record or in
    /// an instantiation slot, as the name `l` it spells, read as a value under
    /// `frame`. The tile is a piece of its entry's form, so the sweep never
    /// classifies it as a form of its own.
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
    fn pun(
        &mut self,
        label: Placed,
        frame: Frame,
    ) -> Result<(), LoweringRefusal<'source>>;

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

    /// The region binder `name` names at `at`: the binder of that name in the
    /// telescope of the definition owning `at`.
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
    fn region_binder(
        &self,
        at: NodeIndex,
        name: SurfaceName<'source>,
    ) -> Option<RegionBinder>;

    /// `ty`, a computation type read under `from` in `telescope`, carried into
    /// the term context of `from` and then under `lift` more binders, each node
    /// it rewrote reported into `copies` when given.
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
    fn relocate(
        &self,
        arena: &mut CoreArena,
        ty: CompTypeId,
        from: Frame,
        telescope: Telescope,
        lift: Binders,
        copies: Option<&mut Vec<Carried>>,
    ) -> CompTypeId;

    /// `ty`, a value type read under `frame` in `telescope`, carried into the
    /// term context of the same frame.
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
    fn relocate_value_type(
        &self,
        ty: ValueTypeId,
        frame: Frame,
        telescope: Telescope,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId;

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

    /// The count a resident of `ua[n, k]`, `compose[n, k]` or `fill[n, k]`
    /// writes, a degree or a catalogue bound, or the cell count of the chain
    /// `chain(m)` names.
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
    fn resident<Count>(
        &self,
        site: Site,
        resident: Placed,
    ) -> Result<Count, LoweringRefusal<'source>>
    where
        Count: From<usize> + PartialEq;

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

    /// Classify the session type whose outermost session form is at `site`.
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
    fn session_type(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>;

    /// The positions of the operands that the key `kept` names, for a read that
    /// walks them by position; no position for a key the store does not hold
    /// whole.
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
    fn spread(
        &self,
        kept: FormStretch,
    ) -> Stretch;

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

    /// The type component or type member `name` names at `site`.
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
    fn stated_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<TypeComponent<'source>, named::Absent>, LoweringRefusal<'source>>;

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

    /// The type a list or a tuple at `site` is written at, and the answer it
    /// was read off when it is answered rather than written.
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
    fn stated_value(
        &mut self,
        site: Site,
    ) -> Result<(Option<NodeIndex>, Option<native::Answer>), LoweringRefusal<'source>>;

    /// The slot `slot`'s carrier, its one unfixed unindexed sort, beside the
    /// type `supplied` gives it.
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
    fn supplied_carrier(
        &self,
        slot: &ModelSlot,
        supplied: &Supplied,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<(Name, ValueTypeId), lowered::Absent>;

    /// Refuse the use at `site` of the declaration `constant` when the
    /// declaration has implicits and the use supplies none.
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
    fn supplied_or_refused(
        &self,
        site: Site,
        constant: ConstantIndex,
    ) -> Result<(), LoweringRefusal<'source>>;

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

    /// The telescope a type at `node` counts its binders in: a body quote's
    /// own when `node` lies in a body quote, the signature's otherwise (#547).
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
    fn telescope_at(
        &self,
        node: NodeIndex,
    ) -> Telescope;

    /// The slot of the theory the path `theory` names, its refusals placed at
    /// `named`, read where a form starting at `at` reads it, each sort `sorts`
    /// names fixed to the type written beside it.
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
    fn theory_slot(
        &mut self,
        named: Site,
        theory: &crate::form::WrittenPath,
        at: ByteOffset,
        sorts: &[(Placed, Placed)],
    ) -> Result<ModelSlot, LoweringRefusal<'source>>;

    /// Read the entries of a type list up to `closer`: each a bare type, or
    /// `k : T` whose key is a bare word, lowercase or named as a type is. A
    /// builtin type's lowercase name, `f32`, is such a word.
    /// Several words before one `:` share its type, `m n : T`, and give one
    /// entry each, in written order.
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
    fn type_entries(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
        closer: TileName,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>;

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

    /// The universe the `Type` tile at `cursor` and the bracket after it spell,
    /// the cursor left past them.
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
    fn universe_tiles(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>;

    /// The form `node` writes once its parentheses are stripped: its former,
    /// the first tile it is written with and its operands.
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
    fn unwrapped(
        &mut self,
        node: NodeIndex,
    ) -> Result<Maybe<Unwrapped, inherited::Absent>, LoweringRefusal<'source>>;

    /// The carrier and the point of `words`: the family's type, and the closed
    /// term the point spells over it, before any wrapping in reflexivity.
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
    fn words_point(
        &self,
        arena: &mut CoreArena,
        words: &WordsForm,
    ) -> Maybe<(ValueTypeId, ValueId), lowered::Absent>;

    /// Whether `at` is written as a group of outputs, the operand of `-F (A,
    /// B)`: a parenthesised type of no entry, several, or one labelled entry.
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
    fn written_group(
        &mut self,
        at: Placed,
        frame: Frame,
    ) -> Result<Grouped, LoweringRefusal<'source>>;

    /// What the form at `at`, not yet classified, states to a call a binder
    /// declared at it heads: the reading `Self::type_application` gives it,
    /// taken without classifying it.
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
    fn written_stack(
        &mut self,
        at: NodeIndex,
    ) -> Result<capability::Stated, LoweringRefusal<'source>>;

    /// The telescope type `node` writes, read through parentheses.
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
    fn written_telescope(
        &mut self,
        node: NodeIndex,
    ) -> Result<Option<NodeIndex>, LoweringRefusal<'source>>;
}
