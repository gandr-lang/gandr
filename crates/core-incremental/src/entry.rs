//! The table parts of an item that its judgement entered elaborated, kept as
//! content beside its typing, and their seat in an edited arena.
//!
//! # The parts
//!
//! A judgement enters an item elaborated when the table holds the item in
//! another form than the written one ([`Entered::Elaborated`]). Then the
//! table holds up to four parts that the written item does not give:
//!
//! - the judged body, which is the item's definition;
//! - the declared type that the table records: the written signature filled
//!   with the solutions of the implicits that the body omits, or its plain type
//!   when the definition binds stages;
//! - the stage signature of a definition that binds stages;
//! - the position of the parameter whose stage the definition's result follows.
//!
//! The body and the declared type are nodes of the judgement's arena, so the
//! entry keeps each as its content table ([`TypeContent`]). The stage
//! signature and the following position name no arena node, so the entry
//! keeps each as the kernel term vocabulary spells it. The entry keeps no
//! part that the table holds as the item writes it: the edited item gives
//! that part.
//!
//! # The seat
//!
//! A seat mints the body and the declared type into an edited arena through
//! [`TypeContent::mint`], each distinct node once. The stage signature and
//! the following position need no seat.

use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::DeclarationContent;
use gandr_core_checker::Entered;
use gandr_core_checker::Verdict;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::StageSignature;
use gandr_kernel_term::StagedPosition;
use quenchant_shape::shape::Maybe;

use crate::content::ArenaNode;
use crate::content::Minted;
use crate::content::Opacity;
use crate::content::Placer;
use crate::content::TypeContent;
use crate::content::TypeMemo;
use crate::content::seating;
use crate::region::Layout;
use crate::region::Program;

quenchant_shape::reason_enum! {
    /// Why a checkpoint keeps no table parts of its item.
    pub mod elaborated {
        /// The reason no table parts are kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The judgement entered the item as written, or the maker of the
            /// checkpoint kept no table parts for it.
            AsWritten,
            /// The item is opaque: no pass adopts or takes its checkpoint, so
            /// no seat reads the parts that it would keep.
            Opaque,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an entry keeps no content for one of its parts.
    pub mod written {
        /// The reason no content is kept for the part.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The table holds the part as the item writes it, or holds none
            /// of it: the edited item gives the part.
            Written,
        }
    }
}

/// The table parts of an item that its judgement entered elaborated: each
/// part that the table holds in another form than the item writes it.
///
/// # Specification
/// - executable: none — this declaration has no call boundary; the judgement
///   whose table it reads is external.
///
/// # Adequacy
/// - hypothesis: L3 — an item whose omitted implicit the judgement fills keeps
///   the filled body and no other part, and the body minted into the program
///   has the content kept; an item entered as written keeps none.
/// - witness: `entry::tests::an_elaborated_item_keeps_its_filled_body_and_mints_it_back`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EntryContent
{
    /// The judged body, which is the item's definition.
    body: Maybe<TypeContent, written::Absent>,
    /// The declared type that the table records.
    declared: Maybe<TypeContent, written::Absent>,
    /// The stage signature of a definition that binds stages.
    stage: Maybe<StageSignature, written::Absent>,
    /// The position of the parameter whose stage the result follows.
    following: Maybe<StagedPosition, written::Absent>,
}

/// The body and the declared type of an entry, minted into an edited arena.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SeatedEntry
{
    /// The judged body, minted.
    body: Maybe<ValueId, written::Absent>,
    /// The declared type that the table records, minted.
    declared: Maybe<ValueTypeId, written::Absent>,
}

impl EntryContent
{
    /// The table parts of `declaration`, which the judgement in `context`
    /// decided with `verdict` and entered as `entered`, each node read through
    /// `layout` and each type through `types`, beside the place of each node
    /// of the judged body in the body's table when the entry keeps the body.
    ///
    /// # Specification
    /// - requires: `context` has just judged `declaration`, and no later
    ///   declaration changed its table.
    /// - ensures: `elaborated::Absent::AsWritten` for an item entered as
    ///   written, `elaborated::Absent::Opaque` for an opaque one; otherwise
    ///   each part that the table holds in another form than the item writes
    ///   it, as content, and the places of the body's table when it keeps the
    ///   body.
    /// - panics: none.
    /// - executable: none — a predicate would read the table again through the
    ///   reads this call makes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`EntryContent`].
    /// - witness: `entry::tests::an_elaborated_item_keeps_its_filled_body_and_mints_it_back`
    pub(crate) fn of(
        context: &CheckingContext<'_>,
        (layout, types): (&Layout, &TypeMemo),
        declaration: &Declaration,
        (verdict, entered, opacity): (Verdict, Entered, Opacity),
    ) -> Maybe<(Self, Option<Placer>), elaborated::Absent>
    {
        match (entered, opacity) {
            (Entered::AsWritten, Opacity::Transparent | Opacity::Opaque) => {
                return Maybe::Absent(elaborated::Absent::AsWritten);
            },
            (Entered::Elaborated, Opacity::Opaque) => {
                return Maybe::Absent(elaborated::Absent::Opaque);
            },
            (Entered::Elaborated, Opacity::Transparent) => {},
        }
        let (signature, body) = match *declaration.content() {
            DeclarationContent::Value { signature, body } => (signature, body),
            DeclarationContent::Data(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World(_)
            | DeclarationContent::Codata(_) => {
                return Maybe::Absent(elaborated::Absent::AsWritten);
            },
        };
        let judged = match verdict {
            Verdict::Checked { body: judged, .. } | Verdict::Synthesised { body: judged, .. } => {
                judged
            },
            Verdict::Data | Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_) => {
                return Maybe::Absent(elaborated::Absent::AsWritten);
            },
        };
        let arena = context.arena();
        let constant = declaration.constant();
        let (body, placer) = if body == Maybe::Present(judged) {
            (Maybe::Absent(written::Absent::Written), None)
        }
        else {
            let (content, placer) = TypeContent::placed(arena, layout, ArenaNode::Value(judged));
            (Maybe::Present(content), Some(placer))
        };
        let declared = match (signature, context.signature(constant)) {
            (Maybe::Present(written), Maybe::Present(formed)) if formed.id() != written => {
                Maybe::Present(types.content(arena, layout, ArenaNode::ValueType(formed.id())))
            },
            (Maybe::Present(_) | Maybe::Absent(_), Maybe::Present(_) | Maybe::Absent(_)) => {
                Maybe::Absent(written::Absent::Written)
            },
        };
        let stage = context
            .stage_signatures()
            .get(&constant)
            .map_or(Maybe::Absent(written::Absent::Written), |stage| {
                Maybe::Present(stage.clone())
            });
        let following = context
            .followings()
            .get(&constant)
            .map_or(Maybe::Absent(written::Absent::Written), |&position| {
                Maybe::Present(position)
            });
        Maybe::Present((
            Self {
                body,
                declared,
                stage,
                following,
            },
            placer,
        ))
    }

    /// The entry of these parts, as the decoder reassembles it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn from_parts(
        (body, declared): (
            Maybe<TypeContent, written::Absent>,
            Maybe<TypeContent, written::Absent>,
        ),
        (stage, following): (
            Maybe<StageSignature, written::Absent>,
            Maybe<StagedPosition, written::Absent>,
        ),
    ) -> Self
    {
        Self {
            body,
            declared,
            stage,
            following,
        }
    }

    /// The judged body as content, when it is not the written body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn body(&self) -> Maybe<&TypeContent, written::Absent>
    {
        match self.body {
            Maybe::Present(ref content) => Maybe::Present(content),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The declared type that the table records as content, when it is not
    /// the written signature.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn declared(&self) -> Maybe<&TypeContent, written::Absent>
    {
        match self.declared {
            Maybe::Present(ref content) => Maybe::Present(content),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The stage signature of a definition that binds stages.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn stage(&self) -> Maybe<&StageSignature, written::Absent>
    {
        match self.stage {
            Maybe::Present(ref stage) => Maybe::Present(stage),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The position of the parameter whose stage the definition's result
    /// follows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn following(&self) -> Maybe<StagedPosition, written::Absent>
    {
        self.following
    }

    /// Mint the body and the declared type into `arena`, their references
    /// placed through `layout`, beside the node minted at each place of the
    /// body's table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, each kept part minted as [`TypeContent::mint`]
    ///   mints it, the body a value and the declared type a value type, and
    ///   each part not kept absent for the reason the entry keeps; the body's
    ///   places minted when the entry keeps the body.
    /// - fails: as [`TypeContent::mint`], and [`seating::Absent::IllSorted`]
    ///   for a body that is no value or a declared type that is no value type.
    /// - panics: none.
    /// - executable: none — a predicate would encode the minted nodes again,
    ///   which the witness does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`EntryContent`].
    /// - witness: `entry::tests::an_elaborated_item_keeps_its_filled_body_and_mints_it_back`
    pub(crate) fn seat(
        &self,
        arena: &mut CoreArena,
        layout: &Layout,
    ) -> Maybe<(SeatedEntry, Option<Minted>), seating::Absent>
    {
        let (body, places) = match self.body {
            Maybe::Present(ref content) => match content.mint_placed(arena, layout) {
                Maybe::Present((ArenaNode::Value(id), places)) => {
                    (Maybe::Present(id), Some(places))
                },
                Maybe::Present((
                    ArenaNode::Computation(_) | ArenaNode::ValueType(_) | ArenaNode::CompType(_),
                    _,
                )) => return Maybe::Absent(seating::Absent::IllSorted),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Maybe::Absent(reason) => (Maybe::Absent(reason), None),
        };
        let declared = match self.declared {
            Maybe::Present(ref content) => match content.mint_value_type(arena, layout) {
                Maybe::Present(id) => Maybe::Present(id),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        Maybe::Present((SeatedEntry { body, declared }, places))
    }

    /// Mint the body and the declared type into `program`'s arena under its
    /// layout.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`EntryContent::seat`] into the program's arena.
    /// - panics: none.
    /// - executable: none — as [`EntryContent::seat`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`EntryContent`].
    /// - witness: `entry::tests::an_elaborated_item_keeps_its_filled_body_and_mints_it_back`
    #[inline]
    pub fn seat_in(
        &self,
        program: &mut Program,
    ) -> Maybe<SeatedEntry, seating::Absent>
    {
        let (arena, layout) = program.parts_mut();
        self.seat(arena, layout).map(|(seated, _)| seated)
    }
}

impl SeatedEntry
{
    /// The judged body, minted, when the entry keeps it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn body(&self) -> Maybe<ValueId, written::Absent>
    {
        self.body
    }

    /// The declared type that the table records, minted, when the entry keeps
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn declared(&self) -> Maybe<ValueTypeId, written::Absent>
    {
        self.declared
    }
}

#[cfg(test)]
mod tests;
