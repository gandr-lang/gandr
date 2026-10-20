//! Located forms in the lowering: the handle type `A at w`, the hold `hold
//! v`, the opening statement `leta x = v ;` and the migration `migrate [w] {
//! t }`.
//!
//! # A world is named by its declaration
//!
//! Every position that reads a world — a handle type's, a migration's and an
//! entry's — reads a name, resolved as any name is: the innermost binder
//! carrying it, else an earlier declaration. A declaration is the world its
//! admission position names, `World::Declared`; whether that declaration
//! declares a world is the checker's to decide, so a name that resolves to a
//! function is refused there, by the checker's own name for it, at the form
//! that wrote it. A binder names no world, and a name nothing binds is
//! [`LoweringRefusal::UnresolvedName`], as an unbound capability region's is.
//! `T at c` reads its name first: a capability scope binding `c` keeps the
//! capability region reading, so the two at types share their spelling.
//!
//! # Each form lowers to its world form
//!
//! `hold v` is a computation returning the handle, read as a value where a
//! value stands by the nesting every computation there takes. `leta x = v ;`
//! opens the handle over the rest of its block, binding `x` intuitionistically
//! as `run x <- c ;` does, so the rest's indices shift as a bind's do.
//! `migrate [w] { t }` reads its block where the migration stands, its last
//! computation the result returned to the world it left. The capability a
//! migration spends is no term: the checker's entry introduces it.
//!
//! - Alternatives: `leta` as a value form, `leta x = v in t`, which the grammar
//!   does not write; a world named by a binder, which presupposes world
//!   variables no consumer needs yet.
//! - Reversal: world variables — the name resolves to a binder as well.
//!
//! A block statement that opens with `hold` is the access statement `hold x
//! = v ;`, so a handle made at a block's tail is written in parentheses,
//! `(hold v)`.
//!
//! # The mark and the entry are written where the source already decides
//!
//! `mobile type T` marks an abstract component of a sealed signature, which
//! is where its representation is hidden, so the claim that the
//! representation crosses sits beside the seal it is checked against; it
//! lowers to [`crate::module::Mark`] on the component's sealing. An entry is
//! the attribute `@[ entry((home, w, …)) ]`, its home first and then the
//! world of each capability, filed as constants under the declaration's keys
//! ([`crate::LoweredModule::worlds`]); a host's own entry is named by the
//! driver and bounds every stated one.
//!
//! - Alternatives: the mark as an attribute, `@[ mobile ]`, which would sit on
//!   the member rather than the signature that seals it; an entry written as a
//!   declaration form, which would need a keyword for what only a host grants.
//! - Reversal: an attribute on signature components, or entries inferred from
//!   the migrations a body makes.

use anodized::spec;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
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
use super::closed;
use super::exhausted;
use super::exits;
use super::lowered;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::origin::Origin;
use crate::resolve::Frame;

#[cfg(test)]
mod tests;

/// A located form or type, as the classification read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each node names a child of the form; a migration's body reads
///   where the migration stands.
/// - executable: none — the plan holds no tree to resolve its nodes in.
///
/// # Adequacy
/// - hypothesis: L3 — a handle type, a hold and a migration each lower to the
///   core form they name.
/// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Worlded
{
    /// `A at w`.
    At
    {
        /// The held type `A`.
        inner: NodeIndex,
        /// The world `w` names.
        world: World,
    },
    /// `hold v`.
    Hold
    {
        /// The value held.
        value: NodeIndex,
    },
    /// `migrate [w] { t }`.
    Migrate
    {
        /// The world `w` names.
        world: World,
        /// The block run there.
        body: Block,
    },
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a located computation: `hold v` or `migrate [w] { t }`.
    ///
    /// # Specification
    /// - requires: `site` is a hold or a migration.
    /// - ensures: the form stands as a computation; a hold's value is read as a
    ///   value under the form's frame; a migration's world is the one its name
    ///   resolves to and its block is read under the form's frame, the block's
    ///   last computation its result.
    /// - fails: the wrong-sort refusal where no computation is read;
    ///   [`LoweringRefusal::UnresolvedName`] for a world name no earlier
    ///   declaration answers; a misplaced-tile fault for a form out of shape;
    ///   the hole's and the block's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold and a migration lower to their world forms,
    ///   and a migration to a name nothing declares is refused at the name.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    /// - witness: `lower::world::tests::a_world_named_where_none_is_declared_is_unresolved`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::World(Worlded::Hold { .. } | Worlded::Migrate { .. }))))]
    pub(super) fn world_form(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let mut cursor = Cursor::new(&pieces.pieces, site.at.span);
        let Maybe::Present(Piece::Tile { label: keyword, .. }) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let worlded = if keyword == TileName::HOLD {
            let value = site.one(cursor.operands())?;
            exhausted(site, &cursor)?;
            self.read(value.node, Reading::Value(frame));
            Worlded::Hold { value: value.node }
        }
        else if keyword == TileName::MIGRATE {
            closed(site, &mut cursor, TileName::BRACKET_OPEN)?;
            let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
            let world = self.world_named(site, frame, written)?;
            let body = self.block(site, &mut cursor, frame)?;
            let _result = self.results.insert(body.last);
            Worlded::Migrate { world, body }
        }
        else {
            return Err(site.fault(site.at.span, FormFault::MisplacedTile));
        };
        self.plan(site, Plan::World(worlded));

        Ok(())
    }

    /// Classify the handle type `T at w`, `w` resolved to the declaration at
    /// `constant`.
    ///
    /// # Specification
    /// - requires: `site` is an at type read as a value type; `operand` is its
    ///   held type.
    /// - ensures: the type stands as the handle to a value of the operand at
    ///   the world the declaration names, the operand read where the at type
    ///   stands.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Errors
    /// None; the result is the shape [`Self::at_type`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handle at a declared world mints the handle type.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(ensures: |ret| ret.is_ok() && matches!(self.plans.get(site.at.node), Some(&Plan::World(Worlded::At { inner, world: World::Declared(declared) })) if inner == operand.node && declared == constant))]
    pub(super) fn located_type(
        &mut self,
        site: Site,
        operand: Placed,
        constant: ConstantIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.read(operand.node, site.reading);
        self.plan(
            site,
            Plan::World(Worlded::At {
                inner: operand.node,
                world: World::Declared(constant),
            }),
        );

        Ok(())
    }

    /// The world the name written at `written` names, read under `frame` by
    /// the form at `site`.
    ///
    /// # Specification
    /// - requires: `written` is an identifier tile of the form at `site`.
    /// - ensures: the world an earlier declaration of the name declares, by its
    ///   admission position.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at the name for a name
    ///   nothing binds or a binder carries; the name's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared world resolves to its position and an
    ///   undeclared name is refused at its span.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    /// - witness: `lower::world::tests::a_world_named_where_none_is_declared_is_unresolved`
    #[spec(ensures: |ret| match ret {
        | Err(LoweringRefusal::UnresolvedName { span, .. }) => span == written.span,
        | Ok(World::Declared(_)) | Err(_) => true,
        | Ok(World::Host) => false,
    })]
    fn world_named(
        &mut self,
        site: Site,
        frame: Frame,
        written: Placed,
    ) -> Result<World, LoweringRefusal<'source>>
    {
        let name = self.name_at(written);
        match self.resolve_name(site, frame, name)? {
            Maybe::Present(Resolved::Declaration { constant, .. }) => Ok(World::Declared(constant)),
            Maybe::Present(Resolved::Binder(_)) | Maybe::Absent(_) => {
                Err(LoweringRefusal::UnresolvedName {
                    span: written.span,
                    name,
                })
            },
        }
    }

    /// Read one `leta x = v ;` statement, its `leta` tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's tile `leta`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: `v` is read as a value under `frame`; the statement is
    ///   recorded as the opening of `v` over the rest of the block, and the
    ///   frame binding `x` intuitionistically over `frame`, which the rest of
    ///   the block reads under, is returned.
    /// - fails: a fault naming the statement for a tile out of shape, the value
    ///   hole's own fault and the binder's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `leta` binds its name over the rest of its block,
    ///   which reads it as the innermost variable.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(
        captures: before = self.statements.len(),
        ensures: |ret| ret.is_err() || (self.statements.len() == before.saturating_add(1)
            && self.statements.last().is_some_and(|last| last.origin == leta.node && matches!(last.binding, StatementBinding::Opened { .. }))),
    )]
    pub(super) fn leta(
        &mut self,
        cursor: &mut Cursor<'_>,
        leta: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: leta,
            name: FormName::LETA_STATEMENT,
            reading: Reading::Computation(frame),
        };
        let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
        };
        closed(statement, cursor, TileName::EQUALS)?;
        let value = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::SEMICOLON)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        self.read(value.node, Reading::Value(frame));
        self.statements.push(Statement {
            origin: leta.node,
            bound: leta.node,
            binding: StatementBinding::Opened {
                value: value.node,
                name: binder.node,
            },
            rest: exits::Rest::Bound,
        });

        Ok(Frame::Inner(self.scope.extend(
            frame,
            name,
            Maybe::Present(binder.span),
        )))
    }

    /// Mint the located form or type `worlded` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the world type or form over its children's lowered nodes at
    ///   `origin`, a migration's block minted as a block; the first absence
    ///   among the children otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handle type, a hold and a migration, each minted at
    ///   its own origin.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(ensures: |ret| match (worlded, ret) {
        | (Worlded::At { .. }, Maybe::Present(Lowered::ValueType(id))) => sink.origins.value_type(id) == Maybe::Present(origin),
        | (Worlded::Hold { .. } | Worlded::Migrate { .. }, Maybe::Present(Lowered::Computation(id))) => sink.origins.computation(id) == Maybe::Present(origin),
        | (_, Maybe::Present(_)) => false,
        | (_, Maybe::Absent(_)) => true,
    })]
    pub(super) fn mint_world(
        &self,
        worlded: Worlded,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let form = match worlded {
            Worlded::At { inner, world } => {
                return self.value_type_at(inner).map(|inner| {
                    let id = sink.arena.value_type_world(WorldType::At { inner, world });
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                });
            },
            Worlded::Hold { value } => match self.value_at(value) {
                Maybe::Present(value) => WorldForm::Hold { value },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Worlded::Migrate { world, body } => match self.mint_block(body, sink) {
                Maybe::Present(body) => WorldForm::Migrate { world, body },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
        };
        let id = sink.arena.computation_world(form);

        Maybe::Present(sink.computation(id, origin))
    }
}
