//! The binary session forms in the lowering: the session type a protocol is
//! written as, the actions on an endpoint, and the statements that bind one.
//!
//! # A session type is read whole, at its root
//!
//! A session type is one core value type: a protocol, one node per state,
//! over the payload types its sends and receives carry. The lowering reads
//! it from its outermost session form — `!A. S`, `?A. S`, `end`, `mu t. S`,
//! or braces whose entries are all session forms — down through every
//! continuation, and plans the protocol there. A continuation is a state of
//! that protocol, never a type of its own, so the sweep does not read it; a
//! payload `A` is an ordinary value type, read where it stands, so a payload
//! names a module's type component as any type does.
//!
//! Inside a protocol the sum over labels `+{…}` is the select and the lazy
//! record over labels `&{…}` the offer, whatever their entries look like, so
//! `next : turn` and `retire : end` read as branches; at a type's root the
//! braces are the select or the offer exactly when every entry is a session
//! form (the `lower::arity` module). A branch is labelled; a positional entry
//! has no label to select. `mu t.` binds `t` for the continuations under it,
//! and a continuation spelled as a name is the innermost binder of that name;
//! any other type standing where a continuation is read is refused by sort,
//! the session continuation. A protocol whose recursion reaches its own
//! variable before any action, `mu t. t`, is refused as not contractive where
//! the `mu` is written.
//!
//! - Alternatives: a core type per continuation, which mints one protocol per
//!   state and makes the protocol's identity depend on sharing; second grammar
//!   rules for the select and the offer, which the grammar declined so one
//!   former is read in the zone it is written in.
//! - Reversal: a continuation naming a session type declared elsewhere — today
//!   refused by sort — would graft that protocol at the name.
//!
//! # An endpoint is a name a fork binds
//!
//! `fork (c : S) { t } as d ;` binds `c` over the child block `t` and `d` over
//! the rest of the enclosing block, each in the linear zone, whose binders a
//! name counts apart from the intuitionistic ones (the `resolve` module): a
//! linear variable's index counts the linear binders between it and its
//! binder, and an intuitionistic one's the intuitionistic binders. An
//! action's endpoint operand is a name resolving to a linear binder; any other
//! operand is refused as no endpoint. An endpoint's name anywhere else is a
//! linear variable, which the checker refuses where a value is read, so
//! delegation is refused there by name.
//!
//! - Alternatives: one binder chain counted across both zones, which gives a
//!   linear variable an index the core's linear zone does not hold; a second
//!   scope for endpoints, which duplicates shadowing and lookup.
//! - Reversal: a core context whose zones share one index space.
//!
//! The child is a process of its own, not a body an exit leaves: `return` and
//! `become` do not stand in it, and it ends with its last computation, such as
//! `close(c)` or `pure unit`, which the checker holds to the pure returner of
//! the unit. Alternative: the child read as a body whose exits leave it, so
//! `return unit` ends it early. Reversal: the same, once a child needs to end
//! from inside a match.
//!
//! # Actions are computations; receipt binds
//!
//! `send(c, v)`, `select(c, l)` and `close(c)` are computations returning the
//! unit, so `send(c, v);` discards that unit as any statement does. `offer(c)
//! { l => t, … }` runs the arm of the label the peer chose, each arm's pattern
//! a label, and passes the paths through it and its answer to each arm as a
//! match does, so an arm may end its function. `recv(c) as x ;` binds the
//! payload over the rest of the block as `run x <- c ;` binds a returned
//! value; the receive is planned at its `recv` keyword, which no other form
//! reads.
//!
//! An early exit commutes through an offer's arms and a fork's parent, which
//! bind no intuitionistic variable (the `lower::exits` module). A fork in a
//! block whose ends an early exit continues is declined as unadmitted: the
//! rest copied to the fork's parent would need its endpoints renumbered past
//! the parent's end, which the commuting does not carry. Reversal: a commuting
//! that relocates linear indices too.
//!
//! # Sharing waits
//!
//! `fork !`, `dup`, `acquire` and `release` are reserved: parsed so they are
//! declined by name, until shared sessions land.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::ChildOrder;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolError;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecursionIndex;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Frame;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Statement;
use super::StatementBinding;
use super::Stretch;
use super::arity::Arranged;
use super::arity::Key;
use super::arity::arrange;
use super::closed;
use super::exhausted;
use super::exits;
use super::lowered;
use super::stretch;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Origin;
use crate::resolve::SurfaceName;

#[cfg(test)]
mod tests;

/// One step of the walk down a protocol: read the form at `at` as the state
/// `state`, or leave the innermost `mu` binder.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a node step names the form and the state it fills.
/// - executable: none — the step holds no draft to check its state against.
///
/// # Adequacy
/// - hypothesis: L3 — the seat's protocol walks every former and leaves its
///   `mu`.
/// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
#[derive(Clone, Copy, Debug)]
enum Walk
{
    /// Read the continuation written at `at` as the state `state`.
    Node
    {
        /// Where the continuation is written.
        at: Placed,
        /// The state it fills.
        state: ProtocolState,
    },
    /// Every continuation under the innermost `mu` has been read.
    Leave,
}

/// A protocol as the walk writes it: one node per state, the form each state
/// is written as, and the steps still to take.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one written form per node, at the node's state.
/// - executable: none — [`Draft::queue`] keeps the two lists aligned.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Walk`].
/// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
#[derive(Debug)]
struct Draft
{
    /// The nodes, a placeholder `end` until the state is read.
    syntax: Vec<ProtocolSyntax>,
    /// The form each state is written as.
    written: Vec<Placed>,
    /// Every place the source writes a state at: each continuation, the form
    /// inside its parentheses, each branch's label and each `mu`'s variable.
    sites: Vec<StateSite>,
    /// The steps of the walk still to take, the last first.
    work: Vec<Walk>,
    /// The operand-store position of the protocol's first payload, which
    /// slot zero names.
    base: usize,
}

/// A place the source writes a protocol's state at.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `state` is a state of the protocol the site was read in.
/// - executable: none — the site holds no protocol to check its state against.
///
/// # Adequacy
/// - hypothesis: L3 — each continuation answers at its own state, and each
///   branch label and `mu` variable at the state it names.
/// - witness: `lower::session::tests::each_state_answers_where_it_is_written`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StateSite
{
    /// Where the source writes it.
    at: Placed,
    /// The state written there.
    state: ProtocolState,
    /// Whether the site is the state's own form or a name for it.
    naming: Naming,
}

/// Whether a site writes a state or names one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Naming
{
    /// The state's own form, a session type standing where it is written.
    Form,
    /// A branch's label or a `mu`'s variable, naming the state it continues
    /// with or binds.
    Label,
}

/// What a session type's mint needs beside its protocol: every site a state
/// is written at, and the frame its payloads are read under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: every site names a state of the protocol it is planned with.
/// - executable: none — the record holds no protocol.
///
/// # Adequacy
/// - hypothesis: L3 — as [`StateSite`].
/// - witness: `lower::session::tests::each_state_answers_where_it_is_written`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Written
{
    /// The sites, in the order the walk read them.
    sites: Vec<StateSite>,
    /// The frame the protocol is read under.
    frame: Frame,
}

impl Draft
{
    /// A fresh state written at `at`, queued for the walk to read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the state one past every earlier one, written at `at`, and
    ///   the step that reads it on top of the walk.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's protocol allocates one state per form.
    /// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
    #[spec(
        captures: before = self.syntax.len(),
        ensures: |ret| usize::from(ret) == before
            && self.syntax.len() == before.saturating_add(1)
            && self.written.last() == Some(&at)
            && matches!(self.work.last(), Some(&Walk::Node { at: queued, state }) if queued == at && state == ret),
    )]
    fn queue(
        &mut self,
        at: Placed,
    ) -> ProtocolState
    {
        let state = ProtocolState::from(self.syntax.len());
        self.syntax.push(ProtocolSyntax::End);
        self.written.push(at);
        self.work.push(Walk::Node { at, state });
        state
    }

    /// Write `node` as the state `state`.
    ///
    /// # Specification
    /// - requires: `state` was made by [`Self::queue`].
    /// - ensures: the state holds `node`; nothing else changes.
    /// - fails: never; a state past the draft is left unwritten.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::queue`].
    /// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
    #[spec(
        captures: expected = node.clone(),
        ensures: |()| self.syntax.get(usize::from(state)).is_none_or(|held| *held == expected),
    )]
    fn fill(
        &mut self,
        state: ProtocolState,
        node: ProtocolSyntax,
    )
    {
        if let Some(held) = self.syntax.get_mut(usize::from(state)) {
            *held = node;
        }
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify the session type whose outermost session form is at `site`.
    ///
    /// # Specification
    /// - requires: `site` is a session form, or braces whose entries are all
    ///   session forms, at a value-type position or quoted at a value one.
    /// - ensures: one protocol over every continuation under `site`, its root
    ///   the state `site` is written as; each payload type read as a value type
    ///   under the form's frame and stored in written order; the continuations
    ///   themselves left unread. Inside the protocol braces are the select and
    ///   the offer over their labelled entries, a `mu` binds its variable for
    ///   the continuations under it, and a name is the innermost binder of that
    ///   name.
    /// - fails: the wrong-sort refusal where no value type is read, and at a
    ///   continuation, by the continuation's sort, for a form no session reads;
    ///   a misplaced tile at a positional branch; a label written twice;
    ///   [`FragmentBoundary::NonContractive`] at a `mu` whose body is a `mu` or
    ///   a variable; each form's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The session type's refusal.
    ///
    /// # Termination
    /// - reason: the walk pops one step per round and pushes the continuations
    ///   of one form, each a strict subtree of it.
    /// - measure: the forms under `site`, each read once, and one leave per
    ///   `mu`.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's protocol, every former reached once, a
    ///   bare variable under its `mu`, a positional branch and a type standing
    ///   as a continuation, each asserted as the exact protocol or refusal.
    /// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
    /// - witness: `lower::session::tests::a_malformed_protocol_is_refused_where_it_is_written`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Session(..))))]
    pub(super) fn session_type(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let mut draft = Draft {
            syntax: Vec::new(),
            written: Vec::new(),
            sites: Vec::new(),
            work: Vec::new(),
            base: self.operands.len(),
        };
        let root = draft.queue(site.at);
        let mut binders: Vec<SurfaceName<'source>> = Vec::new();
        let mut pieces = Pieces::new();
        while let Some(step) = draft.work.pop() {
            self.fuel.spend()?;
            let (at, state) = match step {
                Walk::Leave => {
                    let _left = binders.pop();
                    continue;
                },
                Walk::Node { at, state } => (at, state),
            };
            draft.sites.push(StateSite {
                at,
                state,
                naming: Naming::Form,
            });
            let Some((written, former)) = self.form_at(at)?
            else {
                return Err(site.fault(at.span, FormFault::MisplacedTile));
            };
            let name = match former {
                Former::LabelledSumType => FormName::SELECT_SESSION_TYPE,
                Former::LazyRecordType => FormName::OFFER_SESSION_TYPE,
                Former::Name
                | Former::Constructor
                | Former::Hole
                | Former::Number
                | Former::Text
                | Former::Parenthesized
                | Former::Unit
                | Former::Thunk
                | Former::Lambda
                | Former::Block
                | Former::Return
                | Former::Exit
                | Former::Become
                | Former::Loop
                | Former::While
                | Former::For
                | Former::Break
                | Former::Continue
                | Former::Force
                | Former::Run
                | Former::Call
                | Former::Case
                | Former::Telescope
                | Former::Injection
                | Former::LazyRecord
                | Former::Binary
                | Former::Unary
                | Former::Projection
                | Former::TypeHead
                | Former::TypePath
                | Former::Universe
                | Former::TypeApplication
                | Former::ThunkType
                | Former::ReturnerType
                | Former::ArrowType
                | Former::ProductType
                | Former::SumType
                | Former::LazyProductType
                | Former::TelescopeType
                | Former::ValueFunctionType
                | Former::StaticAbstraction
                | Former::ParenthesizedType
                | Former::PathType
                | Former::CapabilityType
                | Former::Scope
                | Former::Declaration
                | Former::AttributeBlock
                | Former::Import
                | Former::Module
                | Former::Data
                | Former::Instantiation
                | Former::SessionType
                | Former::Action
                | Former::Offer
                | Former::Reserved
                | Former::Unadmitted => written,
            };
            let here = Site {
                at,
                name,
                reading: Reading::ValueType(frame),
            };
            let continuation = LoweringRefusal::OutOfFragment {
                span: at.span,
                form: name,
                sort: FragmentSort::Continuation,
                boundary: FragmentBoundary::WrongSort,
            };
            let node = match former {
                Former::TypeHead => {
                    let named = self.name_at(at);
                    let Some(position) = binders.iter().rposition(|&bound| bound == named)
                    else {
                        return Err(continuation);
                    };
                    let outward = binders.len().saturating_sub(position).saturating_sub(1);
                    ProtocolSyntax::Recur(RecursionIndex::from(outward))
                },
                Former::ParenthesizedType
                | Former::SessionType
                | Former::LabelledSumType
                | Former::LazyRecordType => {
                    read_pieces(self.pbg, self.tree, at.node, &mut pieces)?;
                    if let Maybe::Present(repaired) = pieces.repair {
                        return Err(repaired.refusal(name));
                    }
                    let mut cursor = Cursor::new(&pieces.pieces, at.span);
                    match former {
                        Former::ParenthesizedType => {
                            closed(here, &mut cursor, TileName::PAREN_OPEN)?;
                            let inner = here.one(cursor.operands())?;
                            closed(here, &mut cursor, TileName::PAREN_CLOSE)?;
                            exhausted(here, &cursor)?;
                            draft.work.push(Walk::Node { at: inner, state });
                            continue;
                        },
                        Former::SessionType => {
                            self.session_former(here, state, cursor, &mut draft, &mut binders)?
                        },
                        Former::Name
                        | Former::Constructor
                        | Former::Hole
                        | Former::Number
                        | Former::Text
                        | Former::Parenthesized
                        | Former::Unit
                        | Former::Thunk
                        | Former::Lambda
                        | Former::Block
                        | Former::Return
                        | Former::Exit
                        | Former::Become
                        | Former::Loop
                        | Former::While
                        | Former::For
                        | Former::Break
                        | Former::Continue
                        | Former::Force
                        | Former::Run
                        | Former::Call
                        | Former::Case
                        | Former::Telescope
                        | Former::Injection
                        | Former::LazyRecord
                        | Former::Binary
                        | Former::Unary
                        | Former::Projection
                        | Former::TypeHead
                        | Former::TypePath
                        | Former::Universe
                        | Former::TypeApplication
                        | Former::ThunkType
                        | Former::ReturnerType
                        | Former::ArrowType
                        | Former::ProductType
                        | Former::SumType
                        | Former::LazyProductType
                        | Former::TelescopeType
                        | Former::LabelledSumType
                        | Former::LazyRecordType
                        | Former::ValueFunctionType
                        | Former::StaticAbstraction
                        | Former::PathType
                        | Former::CapabilityType
                        | Former::Scope
                        | Former::Declaration
                        | Former::AttributeBlock
                        | Former::Import
                        | Former::Module
                        | Former::Data
                        | Former::Instantiation
                        | Former::Action
                        | Former::Offer
                        | Former::Reserved
                        | Former::Unadmitted => self.choice(here, former, cursor, &mut draft)?,
                    }
                },
                Former::Name
                | Former::Constructor
                | Former::Hole
                | Former::Number
                | Former::Text
                | Former::Parenthesized
                | Former::Unit
                | Former::Thunk
                | Former::Lambda
                | Former::Block
                | Former::Return
                | Former::Exit
                | Former::Become
                | Former::Loop
                | Former::While
                | Former::For
                | Former::Break
                | Former::Continue
                | Former::Force
                | Former::Run
                | Former::Call
                | Former::Case
                | Former::Telescope
                | Former::Injection
                | Former::LazyRecord
                | Former::Binary
                | Former::Unary
                | Former::Projection
                | Former::TypePath
                | Former::Universe
                | Former::TypeApplication
                | Former::ThunkType
                | Former::ReturnerType
                | Former::ArrowType
                | Former::ProductType
                | Former::SumType
                | Former::LazyProductType
                | Former::TelescopeType
                | Former::ValueFunctionType
                | Former::StaticAbstraction
                | Former::PathType
                | Former::CapabilityType
                | Former::Scope
                | Former::Declaration
                | Former::AttributeBlock
                | Former::Import
                | Former::Module
                | Former::Data
                | Former::Instantiation
                | Former::Action
                | Former::Offer
                | Former::Reserved
                | Former::Unadmitted => return Err(continuation),
            };
            draft.fill(state, node);
        }
        let payloads = Stretch {
            start: draft.base,
            end: self.operands.len(),
        };
        let count = PayloadCount::from(payloads.end.saturating_sub(payloads.start));
        let Draft {
            syntax,
            written,
            sites,
            ..
        } = draft;
        let protocol = match Protocol::new(syntax, root, count) {
            Ok(protocol) => protocol,
            Err(ProtocolError::NonContractive(state)) => {
                let at = written.get(usize::from(state)).copied().unwrap_or(site.at);
                let name = self.form_at(at)?.map_or(site.name, |(name, _former)| name);
                return Err(Site { at, name, ..site }.out(FragmentBoundary::NonContractive));
            },
            Err(_malformed) => return Err(site.out(FragmentBoundary::Unadmitted)),
        };
        self.plan(
            site,
            Plan::Session(
                Arc::new(protocol),
                payloads,
                Arc::new(Written { sites, frame }),
            ),
        );

        Ok(())
    }

    /// Read one of a session type's own forms, `!A. S`, `?A. S`, `end` or `mu
    /// t. S`, at `here`, its continuations queued on the walk.
    ///
    /// # Specification
    /// - requires: `cursor` reads the form's pieces from the start, and `state`
    ///   is the state the form is written as.
    /// - ensures: `end` is the closed node; a send or receive reads its payload
    ///   as a value type under the form's frame, stores it in the next slot and
    ///   queues its continuation as a fresh state; `mu t. S` binds `t` for the
    ///   walk under it, queues a leave after `S`, is the fixed point of the
    ///   state `S` fills, and keeps `t` as a site naming `state`.
    /// - fails: a misplaced tile or a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's protocol reads every one of the four.
    /// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
    #[spec(
        captures: before = (draft.syntax.len(), self.operands.len()),
        ensures: |ret| ret.as_ref().map_or(true, |node| match *node {
            | ProtocolSyntax::Send { payload, next } | ProtocolSyntax::Receive { payload, next } => self.operands.len() == before.1.saturating_add(1) && usize::from(payload) == before.1.saturating_sub(draft.base) && usize::from(next) == before.0,
            | ProtocolSyntax::Mu(body) => usize::from(body) == before.0,
            | ProtocolSyntax::End => draft.syntax.len() == before.0,
            | ProtocolSyntax::Select(_) | ProtocolSyntax::Offer(_) | ProtocolSyntax::Recur(_) => false,
        }),
    )]
    fn session_former(
        &mut self,
        here: Site,
        state: ProtocolState,
        mut cursor: Cursor<'_>,
        draft: &mut Draft,
        binders: &mut Vec<SurfaceName<'source>>,
    ) -> Result<ProtocolSyntax, LoweringRefusal<'source>>
    {
        if let Maybe::Present(_) = cursor.tile(TileName::END) {
            exhausted(here, &cursor)?;
            return Ok(ProtocolSyntax::End);
        }
        if let Maybe::Present(_) = cursor.tile(TileName::MU) {
            let Maybe::Present(variable) = cursor.tile(TileName::TYPE_VARIABLE)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            closed(here, &mut cursor, TileName::DOT)?;
            let body = here.one(cursor.operands())?;
            exhausted(here, &cursor)?;
            binders.push(self.name_at(variable));
            draft.sites.push(StateSite {
                at: variable,
                state,
                naming: Naming::Label,
            });
            draft.work.push(Walk::Leave);
            let inner = draft.queue(body);
            return Ok(ProtocolSyntax::Mu(inner));
        }
        let sends = match cursor.tile(TileName::BANG) {
            Maybe::Present(_) => true,
            Maybe::Absent(_) => {
                closed(here, &mut cursor, TileName::QUESTION)?;
                false
            },
        };
        let carried = here.one(cursor.operands())?;
        closed(here, &mut cursor, TileName::DOT)?;
        let continued = here.one(cursor.operands())?;
        exhausted(here, &cursor)?;
        let Reading::ValueType(frame) = here.reading
        else {
            return Err(here.out(FragmentBoundary::WrongSort));
        };
        let payload = PayloadSlot::from(self.operands.len().saturating_sub(draft.base));
        self.operands.push(carried.node);
        self.read(carried.node, Reading::ValueType(frame));
        let next = draft.queue(continued);

        Ok(if sends {
            ProtocolSyntax::Send { payload, next }
        }
        else {
            ProtocolSyntax::Receive { payload, next }
        })
    }

    /// Read braces inside a protocol as the select, `+{ l : S, … }`, or the
    /// offer, `&{ l : S, … }`, their branches queued on the walk.
    ///
    /// # Specification
    /// - requires: `cursor` reads the braces' pieces from the start; `former`
    ///   is the sum or the lazy record over labels.
    /// - ensures: one fresh state per labelled branch, keyed by its label,
    ///   queued at its continuation and kept with its label as a site naming
    ///   it; the select for the sum, the offer for the lazy record.
    /// - fails: a misplaced tile at a positional branch; a label written twice;
    ///   the braces' own faults.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::DuplicateDefinition`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's select and offer, and a positional branch.
    /// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
    /// - witness: `lower::session::tests::a_malformed_protocol_is_refused_where_it_is_written`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |node| matches!(*node, ProtocolSyntax::Select(_) | ProtocolSyntax::Offer(_)) && matches!(*node, ProtocolSyntax::Select(_)) == (former == Former::LabelledSumType)))]
    fn choice(
        &self,
        here: Site,
        former: Former,
        mut cursor: Cursor<'_>,
        draft: &mut Draft,
    ) -> Result<ProtocolSyntax, LoweringRefusal<'source>>
    {
        let opener = if former == Former::LabelledSumType {
            TileName::PLUS
        }
        else {
            TileName::AMPERSAND
        };
        closed(here, &mut cursor, opener)?;
        closed(here, &mut cursor, TileName::BRACE_OPEN)?;
        let entries = self.type_entries(here, &mut cursor, TileName::BRACE_CLOSE)?;
        let entries = match arrange(here, entries)? {
            Arranged::Labelled(entries) => entries,
            Arranged::Positional(entries) => {
                if let Some(first) = entries.first() {
                    return Err(here.fault(first.held.at().span, FormFault::MisplacedTile));
                }
                entries
            },
        };
        let mut branches = BTreeMap::new();
        for entry in entries.iter().rev() {
            if let Key::Label(label, written) = entry.key {
                let branch = draft.queue(entry.held.at());
                draft.sites.push(StateSite {
                    at: written,
                    state: branch,
                    naming: Naming::Label,
                });
                let _first =
                    branches.insert(FieldLabel::from(String::from(label.as_ref())), branch);
            }
        }

        Ok(if former == Former::LabelledSumType {
            ProtocolSyntax::Select(branches)
        }
        else {
            ProtocolSyntax::Offer(branches)
        })
    }

    /// The linear index of the endpoint `operand` names, the subject of an
    /// action read under `frame`.
    ///
    /// # Specification
    /// - requires: `operand` is the subject hole's operand of an action.
    /// - ensures: the linear index of the innermost binder of the name
    ///   `operand` spells, when that binder is linear; the operand is left
    ///   unread, since no value stands for it.
    /// - fails: [`LoweringRefusal::UnresolvedName`] for a name nothing binds;
    ///   [`FragmentBoundary::Endpoint`] at the operand for any other form, an
    ///   intuitionistic binder or a declaration; the name's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The endpoint's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fork's ends resolve at their linear indices past
    ///   intuitionistic binders between, and a parameter and a literal in the
    ///   subject hole are refused.
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `lower::session::tests::an_action_on_no_endpoint_is_refused`
    #[spec(ensures: |ret| match ret {
        | Err(LoweringRefusal::OutOfFragment { span, boundary, .. }) => boundary != FragmentBoundary::Endpoint || span == operand.span,
        | _ => true,
    })]
    fn endpoint(
        &mut self,
        frame: Frame,
        operand: Placed,
    ) -> Result<DeBruijnIndex, LoweringRefusal<'source>>
    {
        let (name, former) = self
            .form_at(operand)?
            .unwrap_or((FormName::IDENTIFIER, Former::Unadmitted));
        let subject = Site {
            at: operand,
            name,
            reading: Reading::Value(frame),
        };
        if former != Former::Name {
            return Err(subject.out(FragmentBoundary::Endpoint));
        }
        let spelled = self.name_at(operand);
        match self.resolve_name(subject, frame, spelled)? {
            Maybe::Present(Resolved::Binder(bound)) if bound.zone == Zone::Linear => {
                Ok(bound.index)
            },
            Maybe::Present(_) => Err(subject.out(FragmentBoundary::Endpoint)),
            Maybe::Absent(_) => Err(LoweringRefusal::UnresolvedName {
                span: operand.span,
                name: spelled,
            }),
        }
    }

    /// Classify a session action: `send(c, v)`, `select(c, l)`, `close(c)` or
    /// `offer(c) { l => t, … }`.
    ///
    /// # Specification
    /// - requires: `site` is a session action expression.
    /// - ensures: the action on the endpoint its subject names, planned as one
    ///   core action: a send's payload read as a value, a selection's label its
    ///   identifier, an offer's arms each read as a computation under the
    ///   form's frame, keyed by the label its pattern names, with the answer
    ///   and the paths through the offer passed to each.
    /// - fails: the wrong-sort refusal where no computation is read; the
    ///   endpoint's refusal; a pattern other than a label, refused as an
    ///   unadmitted pattern; a label armed twice, as a duplicate definition;
    ///   each hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The action's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every action of the seat exchange, at both ends, an
    ///   offer arming one label twice and an offer arm patterned by a
    ///   constructor.
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `lower::session::tests::an_action_on_no_endpoint_is_refused`
    /// - witness: `lower::session::tests::an_offer_arm_is_one_label`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Action(..))))]
    pub(super) fn session_action(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let Maybe::Present(Piece::Tile { label: keyword, .. }) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(site, &mut cursor, TileName::PAREN_OPEN)?;
        let subject = site.one(cursor.operands())?;
        let action = if keyword == TileName::SEND {
            closed(site, &mut cursor, TileName::COMMA)?;
            let payload = site.one(cursor.operands())?;
            closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
            exhausted(site, &cursor)?;
            let endpoint = self.endpoint(frame, subject)?;
            self.read(payload.node, Reading::Value(frame));
            SessionAction::Send {
                endpoint,
                payload: payload.node,
            }
        }
        else if keyword == TileName::SELECT {
            closed(site, &mut cursor, TileName::COMMA)?;
            let Maybe::Present(chosen) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
            exhausted(site, &cursor)?;
            SessionAction::Select {
                endpoint: self.endpoint(frame, subject)?,
                label: FieldLabel::from(String::from(self.name_at(chosen).as_ref())),
            }
        }
        else if keyword == TileName::CLOSE {
            closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
            exhausted(site, &cursor)?;
            SessionAction::Close {
                endpoint: self.endpoint(frame, subject)?,
            }
        }
        else if keyword == TileName::OFFER {
            closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
            let endpoint = self.endpoint(frame, subject)?;
            self.offer(site, cursor, frame, endpoint)?
        }
        else {
            return Err(site.fault(site.at.span, FormFault::MisplacedTile));
        };
        self.plan(site, Plan::Action(action, subject.span));

        Ok(())
    }

    /// Read an offer's arms, `{ l => t, … }`, on `endpoint`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the offer's `{`.
    /// - ensures: one arm per label, each body read as a computation under
    ///   `frame`, taking the offer's answer and the paths through it.
    /// - fails: a pattern other than a label, refused as an unadmitted pattern;
    ///   a label armed twice, as a duplicate definition; a tile out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// The arms' refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::session_action`].
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `lower::session::tests::an_offer_arm_is_one_label`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |action| matches!(*action, SessionAction::Offer { endpoint: subject, .. } if subject == endpoint)))]
    fn offer(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        frame: Frame,
        endpoint: DeBruijnIndex,
    ) -> Result<SessionAction<NodeIndex, NodeIndex, NodeIndex>, LoweringRefusal<'source>>
    {
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let mut written: Vec<(Placed, Placed)> = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let _bar = cursor.tile(TileName::BAR);
            let pattern = site.one(cursor.operands())?;
            closed(site, &mut cursor, TileName::FAT_ARROW)?;
            let body = site.one(cursor.operands())?;
            written.push((pattern, body));
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                closed(site, &mut cursor, TileName::BRACE_CLOSE)?;
                break;
            }
        }
        exhausted(site, &cursor)?;
        let mut arms: BTreeMap<FieldLabel, NodeIndex> = BTreeMap::new();
        let mut labelled: BTreeMap<SurfaceName<'source>, Placed> = BTreeMap::new();
        for &(pattern, body) in &written {
            let named = self
                .form_at(pattern)?
                .map_or(FormName::HOLE, |(name, _former)| name);
            if named != FormName::IDENTIFIER {
                return Err(LoweringRefusal::OutOfFragment {
                    span: pattern.span,
                    form: named,
                    sort: FragmentSort::Pattern,
                    boundary: FragmentBoundary::Unadmitted,
                });
            }
            let label = self.name_at(pattern);
            if let Some(&first) = labelled.get(&label) {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: pattern.span,
                    name: label,
                    first: first.span,
                });
            }
            let _first = labelled.insert(label, pattern);
            let _armed = arms.insert(FieldLabel::from(String::from(label.as_ref())), body.node);
            self.read(body.node, Reading::Computation(frame));
            if let Some(&answer) = self.answers.get(&site.at.node) {
                let _passed = self.answers.insert(body.node, answer);
            }
            self.pass_paths(site.at.node, body.node);
        }

        Ok(SessionAction::Offer { endpoint, arms })
    }

    /// Read one `recv(c) as x ;` statement, its `recv` tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's tile `recv`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: the receive on the endpoint `c` names is planned at the
    ///   `recv` tile and recorded as a statement binding `x`; the frame binding
    ///   `x` over `frame`, which the rest of the block reads under, is
    ///   returned.
    /// - fails: the endpoint's refusal and a fault naming the receive statement
    ///   for a tile out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's receive binds the dispatch over the rest
    ///   of its block, and the operator's receives under offer arms.
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    #[spec(
        captures: before = self.statements.len(),
        ensures: |ret| ret.is_err() || (self.statements.len() == before.saturating_add(1)
            && self.statements.last().is_some_and(|last| last.origin == recv.node && last.bound == recv.node)
            && matches!(self.plans.get(usize::from(recv.node)), Some(&Plan::Action(SessionAction::Receive { .. }, _)))),
    )]
    pub(super) fn receive(
        &mut self,
        cursor: &mut Cursor<'_>,
        recv: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: recv,
            name: FormName::RECV_STATEMENT,
            reading: Reading::Computation(frame),
        };
        closed(statement, cursor, TileName::PAREN_OPEN)?;
        let subject = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::PAREN_CLOSE)?;
        closed(statement, cursor, TileName::AS)?;
        let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(statement, cursor, TileName::SEMICOLON)?;
        let endpoint = self.endpoint(frame, subject)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        self.plan(
            statement,
            Plan::Action(SessionAction::Receive { endpoint }, subject.span),
        );
        self.statements.push(Statement {
            origin: recv.node,
            bound: recv.node,
            binding: StatementBinding::Named(binder.node),
            rest: exits::Rest::Bound,
        });

        Ok(Frame::Inner(self.scope.extend(
            frame,
            name,
            Maybe::Present(binder.span),
        )))
    }

    /// Read one `fork (c : S) t as d ;` statement, its `fork` tile already
    /// read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's tile `fork`, no
    ///   `!` after it; `frame` is the frame the statement reads under.
    /// - ensures: `S` is read as a value type under `frame` and `t` as a
    ///   computation under `c`'s linear binder over `frame`; the statement is
    ///   recorded as the fork of `t` over the rest of the block, and the frame
    ///   binding `d` linearly over `frame`, which the rest of the block reads
    ///   under, is returned.
    /// - fails: a fault naming the fork statement for a tile out of shape, and
    ///   each binder's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat exchange forks the seat's end to the child
    ///   and holds the operator's in the rest of its block.
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    #[spec(
        captures: before = self.statements.len(),
        ensures: |ret| ret.is_err() || (self.statements.len() == before.saturating_add(1)
            && self.statements.last().is_some_and(|last| last.origin == fork.node && matches!(last.binding, StatementBinding::Forked { .. }))),
    )]
    pub(super) fn fork(
        &mut self,
        cursor: &mut Cursor<'_>,
        fork: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: fork,
            name: FormName::FORK_STATEMENT,
            reading: Reading::Computation(frame),
        };
        closed(statement, cursor, TileName::PAREN_OPEN)?;
        let Maybe::Present(child_end) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(statement, cursor, TileName::COLON)?;
        let protocol = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::PAREN_CLOSE)?;
        let child = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::AS)?;
        let Maybe::Present(parent_end) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(statement, cursor, TileName::SEMICOLON)?;
        let child_name = self.name_at(child_end);
        self.note_binder(child_end, child_name)?;
        let parent_name = self.name_at(parent_end);
        self.note_binder(parent_end, parent_name)?;
        self.read(protocol.node, Reading::ValueType(frame));
        let held = self
            .scope
            .extend_linear(frame, child_name, Maybe::Present(child_end.span));
        self.read(child.node, Reading::Computation(Frame::Inner(held)));
        self.statements.push(Statement {
            origin: fork.node,
            bound: fork.node,
            binding: StatementBinding::Forked {
                protocol: protocol.node,
                child: child.node,
            },
            rest: exits::Rest::Bound,
        });

        Ok(Frame::Inner(self.scope.extend_linear(
            frame,
            parent_name,
            Maybe::Present(parent_end.span),
        )))
    }

    /// Mint a session type over its payload types, and the state each site of
    /// it is written at.
    ///
    /// # Specification
    /// - requires: every payload type is already minted or absent.
    /// - ensures: the session type at `protocol`'s root over the payloads in
    ///   slot order, with the written origin; beside it, for each other site
    ///   that writes a state, that state's session type at the site's bytes,
    ///   and for each label or `mu` variable a label naming its state's session
    ///   type under the protocol's frame; nothing when a payload did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's protocol over its three payloads, and each
    ///   of its continuations, labels and variables at its state.
    /// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
    /// - witness: `lower::session::tests::each_state_answers_where_it_is_written`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_session(
        &self,
        protocol: &Arc<Protocol>,
        payloads: Stretch,
        written: &Written,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let operands = stretch(&self.operands, payloads);
        let mut carried: Vec<ValueTypeId> = Vec::with_capacity(operands.len());
        for &payload in operands {
            match self.value_type_at(payload) {
                Maybe::Present(ty) => carried.push(ty),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let Ok(session) = SessionType::new(Arc::clone(protocol), Arc::from(carried))
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let root = session.state();
        let id = sink.arena.value_type_session(session.clone());
        sink.origins.record_value_type(id, origin);
        let mut states: BTreeMap<ProtocolState, ValueTypeId> = BTreeMap::new();
        let _root = states.insert(root, id);
        let context: Vec<String> = self
            .scope
            .telescope_names(written.frame)
            .into_iter()
            .map(|name| String::from(name.as_ref()))
            .collect();
        for site in &written.sites {
            if site.naming != Naming::Form || site.at.node == origin.node() {
                continue;
            }
            let Ok(at) = session.at(site.state)
            else {
                continue;
            };
            let ty = sink.arena.value_type_session(at);
            sink.origins
                .record_value_type(ty, Origin::new(site.at.node, site.at.span));
            let _first = states.entry(site.state).or_insert(ty);
        }
        // Every state is written somewhere, so each label finds its state's
        // type among the forms minted above.
        for site in &written.sites {
            if site.naming != Naming::Label {
                continue;
            }
            let Some(&ty) = states.get(&site.state)
            else {
                continue;
            };
            sink.origins.record_label(Label {
                span: site.at.span,
                labelled: Labelled::ValueType {
                    ty,
                    context: context.clone(),
                },
            });
        }

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint a session action over its children, its endpoint written at
    /// `subject`.
    ///
    /// # Specification
    /// - requires: every child of `action` is already minted or absent.
    /// - ensures: the action over its children's lowered nodes, with the
    ///   written origin, and a label at `subject` naming the action's endpoint;
    ///   nothing when a child did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every action of the seat exchange, each endpoint
    ///   answering at its action.
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `lower::session::tests::each_endpoint_answers_at_its_action`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    pub(super) fn mint_action(
        &self,
        action: &SessionAction<NodeIndex, NodeIndex, NodeIndex>,
        subject: ByteSpan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let minted = action.try_map(
            ChildOrder::Forward,
            &mut (),
            |&mut (), payload| match self.value_at(payload) {
                Maybe::Present(id) => Ok(id),
                Maybe::Absent(reason) => Err(reason),
            },
            |&mut (), arm| match self.computation_at(arm) {
                Maybe::Present(id) => Ok(id),
                Maybe::Absent(reason) => Err(reason),
            },
            |&mut (), protocol| match self.value_type_at(protocol) {
                Maybe::Present(id) => Ok(id),
                Maybe::Absent(reason) => Err(reason),
            },
        );
        match minted {
            Ok(action) => {
                let id = sink.arena.computation_session(action);
                sink.origins.record_label(Label {
                    span: subject,
                    labelled: Labelled::Endpoint(id),
                });
                Maybe::Present(sink.computation(id, origin))
            },
            Err(reason) => Maybe::Absent(reason),
        }
    }
}
