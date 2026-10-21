//! A method's receiver: the first parameter of a module member, named `self`
//! and written with its type, whose mode word says what a call `s.f(…)` does
//! with the receiver `s`. `self : shared T` reads it through a shared view,
//! `self : T` writes it through an exclusive one and `self : consumed T`
//! takes it.

use quenchant_shape::shape::Maybe;

use crate::SurfaceName;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::Placed;
use crate::form::TileName;

/// The mode a method's receiver is written at.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one mode per mode word, the unwritten word exclusive.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — a plain enumeration.
///
/// # Adequacy
/// - hypothesis: L3 — a method at each mode lowers to the access its mode
///   names.
/// - witness: `lower::method::tests::each_mode_lowers_to_its_access`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReceiverMode
{
    /// `self : shared T`: the call reads the receiver through a shared view.
    Shared,
    /// `self : T`: the call writes the receiver through an exclusive view,
    /// the method returning the value written back beside its result.
    Exclusive,
    /// `self : consumed T`: the call takes the receiver, ending its hold.
    Consumed,
}

/// The mode of the receiver the declaration whose header `header` reads
/// declares, when its first explicit parameter is `self` written with its
/// type.
///
/// # Specification
/// - requires: `header` stands just past the declaration's name; `name_of`
///   reads a tile's name.
/// - ensures: past an implicit telescope `@[…]`, a parameter list whose first
///   parameter is `self : shared T`, `self : T` or `self : consumed T` answers
///   that parameter's mode; anything else answers nothing.
/// - fails: never.
/// - panics: none.
/// - executable: none — the mode is read off the header's tiles, which a
///   postcondition could only restate by reading them again.
///
/// # Adequacy
/// - hypothesis: L3 — a receiver at each mode, one behind an implicit
///   telescope, an untyped `self` and a first parameter of another name.
/// - witness: `lower::method::tests::a_receiver_is_a_typed_first_self`
pub(super) fn receiver_of<'source>(
    header: &Cursor<'_>,
    name_of: impl Fn(Placed) -> SurfaceName<'source>,
) -> Option<ReceiverMode>
{
    let mut cursor = header.clone();
    if let Maybe::Present(_) = cursor.tile(TileName::ATTRIBUTES) {
        loop {
            match cursor.read() {
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACKET_CLOSE => {
                    break;
                },
                Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {},
                Maybe::Absent(_) => return None,
            }
        }
    }
    let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN)
    else {
        return None;
    };
    let Maybe::Present(first) = cursor.tile(TileName::IDENTIFIER)
    else {
        return None;
    };
    if name_of(first).as_ref() != "self" {
        return None;
    }
    let Maybe::Present(_) = cursor.tile(TileName::COLON)
    else {
        return None;
    };

    Some(if let Maybe::Present(_) = cursor.tile(TileName::SHARED) {
        ReceiverMode::Shared
    }
    else if let Maybe::Present(_) = cursor.tile(TileName::CONSUMED) {
        ReceiverMode::Consumed
    }
    else {
        ReceiverMode::Exclusive
    })
}
