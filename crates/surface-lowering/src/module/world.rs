//! World declarations, as the collection pass reads them.
//!
//! `world w ;` takes a slot like any top-level name, its definition half
//! [`Operand::World`](super::Operand::World): the declaration lowers to no core
//! term, and its admission position is the world's identity, which a handle
//! type `A at w`, a migration `migrate [w] { … }` and an entry `@[ entry(…) ]`
//! name. The name enters the module's namespace, so every position that reads a
//! world resolves it as it resolves any earlier declaration, and a world
//! declared twice is the duplicate definition any name declared twice is.
//!
//! `world w requires R ;` files the theory path `R` beside the slot
//! ([`super::Collected::requirements`]): the signature of what a role placed
//! at `w` needs, which a deployment holds each site placing `w` to offer. The
//! path is resolved once every name is collected, as an ascription's theory
//! is.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
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
use crate::resolve::SurfaceName;

/// The requirement a world is written with, `world w requires R ;`: the theory
/// of what a role placed at `w` needs, named as `Model(Gandr.Package)` names
/// one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WorldRequirement<'source>
{
    /// Each module before the theory's name, with its bytes.
    pub prefix: Vec<(ByteSpan, SurfaceName<'source>)>,
    /// The bytes of the theory's name.
    pub span: ByteSpan,
    /// The theory's name.
    pub name: SurfaceName<'source>,
    /// The bytes of the whole path, from its first segment to the theory's
    /// name.
    pub written: ByteSpan,
}

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
    /// - provides: the world half of [`super::collect_source`].
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
        let (written, read) = match read_requirement(&mut cursor) {
            Ok(written) => (written, Ok(())),
            Err(refusal) => (Vec::new(), Err(refusal)),
        };
        let closed = matches!(cursor.tile(TileName::SEMICOLON), Maybe::Present(_))
            && matches!(cursor.peek(), Maybe::Absent(_));
        let tail = if let Maybe::Present(repaired) = pieces.repair {
            Tail::Refused(repaired.refusal(FormName::WORLD_DECLARATION))
        }
        else if let Err(refusal) = attributed {
            Tail::Refused(refusal)
        }
        else if let Err(refusal) = read {
            Tail::Refused(refusal)
        }
        else if !closed {
            Tail::Refused(misplaced_in(FormName::WORLD_DECLARATION, cursor.here()))
        }
        else {
            Tail::World
        };
        if matches!(tail, Tail::World)
            && let (Some(&first), Some((&theory, prefix))) = (written.first(), written.split_last())
            && let Ok(whole) = ByteSpan::new(first.span.start(), theory.span.end())
        {
            let requirement = WorldRequirement {
                prefix: prefix
                    .iter()
                    .map(|&segment| (segment.span, self.name_of(segment)))
                    .collect(),
                span: theory.span,
                name: self.name_of(theory),
                written: whole,
            };
            let _first = self.collected.requirements.insert(slot, requirement);
        }
        self.file(slot, declaration, named, tail, attributes);

        Ok(())
    }
}

/// The theory path after `requires`, read off `cursor` where it stands: each
/// segment's tile, the theory's name last; none when no `requires` follows.
///
/// # Specification
/// - requires: `cursor` stands after a world declaration's name.
/// - ensures: empty, the cursor unmoved, when the next tile is no `requires`;
///   otherwise the type identifier after it and each segment after a `.`, in
///   written order, the cursor past the last.
/// - fails: a `requires` with no type identifier after it, or a `.` with no
///   segment after it.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`] at the tile that stands out of place.
///
/// # Adequacy
/// - hypothesis: L3 — a world written with a bare and with a dotted requirement
///   files each path; one written with none files nothing.
/// - witness: `lower::world::tests::a_world_s_requirement_names_its_theory_3376`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |path| path.is_sorted_by_key(|segment| segment.span.start())))]
fn read_requirement(cursor: &mut Cursor<'_>) -> Result<Vec<Placed>, LoweringRefusal<'static>>
{
    let mut path = Vec::new();
    if let Maybe::Absent(_) = cursor.tile(TileName::REQUIRES) {
        return Ok(path);
    }
    let Maybe::Present(head) = cursor.tile(TileName::TYPE_IDENTIFIER)
    else {
        return Err(misplaced_in(FormName::WORLD_DECLARATION, cursor.here()));
    };
    path.push(head);
    while let Maybe::Present(_) = cursor.tile(TileName::DOT) {
        match cursor.tile(TileName::TYPE_IDENTIFIER) {
            Maybe::Present(segment) => path.push(segment),
            Maybe::Absent(_) => match cursor.tile(TileName::IDENTIFIER) {
                Maybe::Present(segment) => path.push(segment),
                Maybe::Absent(_) => {
                    return Err(misplaced_in(FormName::WORLD_DECLARATION, cursor.here()));
                },
            },
        }
    }

    Ok(path)
}
