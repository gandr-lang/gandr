//! World declarations, as the collection pass reads them.
//!
//! `world w ;` takes a slot like any top-level name, its definition half
//! [`Operand::World`](super::Operand::World): the declaration lowers to no core
//! term, and its admission position is the world's identity, which a handle
//! type `A at w`, a migration `migrate [w] { … }` and an entry `@[ entry(…) ]`
//! name. The name enters the module's namespace, so every position that reads a
//! world resolves it as it resolves any earlier declaration, and a world
//! declared twice is the duplicate definition any name declared twice is.

use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::Collector;
use super::Tail;
use super::misplaced_in;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;

impl<'source> Collector<'_, 'source>
{
    /// Collect the world declaration `declaration`, decorated by the
    /// attribute blocks `decorations` standing before it.
    ///
    /// # Specification
    /// - requires: `declaration` is a world declaration form and every entry of
    ///   `decorations` an attribute block standing on its own before it.
    /// - ensures: the world's name takes its slot in the declaration's source,
    ///   which owns the declaration and its decorations; a clean form files its
    ///   definition half, [`super::Operand::World`], and its attributes; the
    ///   form's first fault is offered to the slot instead.
    /// - provides: the world half of [`super::collect`].
    /// - fails: when the form has no name to file a refusal under.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a nameless declaration and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared world, a world declared twice and a world
    ///   named where none is declared separate filing from refusal.
    /// - witness: `lower::world::tests::a_world_declaration_names_its_world`
    /// - witness: `lower::world::tests::a_world_declared_twice_is_refused`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| ret.is_err() || (self.collected.slots.len() >= before
            && matches!(self.collected.owner_of(declaration.node), Maybe::Present(_))),
    )]
    pub(super) fn world(
        &mut self,
        declaration: Placed,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        let outcome = read_pieces(self.pbg, self.tree, declaration.node, &mut pieces)
            .and_then(|()| self.read_world(declaration, &pieces, decorations));
        self.pieces = pieces;

        outcome
    }

    /// Read the world declaration `declaration` over its pieces.
    ///
    /// # Specification
    /// - requires: as [`Self::world`]; `pieces` is the declaration's reading.
    /// - ensures: as [`Self::world`].
    /// - fails: as [`Self::world`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::world`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::world`].
    /// - witness: `lower::world::tests::a_world_declaration_names_its_world`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.collected.owner_of(declaration.node), Maybe::Present(_)))]
    fn read_world(
        &mut self,
        declaration: Placed,
        pieces: &Pieces,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, declaration.span);
        let _world = cursor.tile(TileName::WORLD);
        let Maybe::Present(named) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(misplaced_in(FormName::WORLD_DECLARATION, cursor.here()));
        };
        let name = self.name_of(named);
        let slot = self.admit(
            self.collected.top(declaration.span.start()),
            name,
            declaration,
            named,
        );
        self.collected.own(declaration.node, slot);
        for &block in decorations {
            self.document(slot, block.node, block.span.end(), declaration.node);
        }
        self.document(slot, declaration.node, named.span.start(), declaration.node);
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in decorations {
            self.collected.own(block.node, slot);
            if attributed.is_ok() {
                attributed = self.decoration(block, declaration.node, &mut attributes);
            }
        }
        let closed = matches!(cursor.tile(TileName::SEMICOLON), Maybe::Present(_))
            && matches!(cursor.peek(), Maybe::Absent(_));
        let tail = if let Maybe::Present(repaired) = pieces.repair {
            Tail::Refused(repaired.refusal(FormName::WORLD_DECLARATION))
        }
        else if let Err(refusal) = attributed {
            Tail::Refused(refusal)
        }
        else if !closed {
            Tail::Refused(misplaced_in(FormName::WORLD_DECLARATION, cursor.here()))
        }
        else {
            Tail::World
        };
        self.file(slot, declaration, tail, attributes);

        Ok(())
    }
}
