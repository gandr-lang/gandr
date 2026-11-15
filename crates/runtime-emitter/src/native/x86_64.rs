//! The x86-64 patcher: the four relocation kinds the ELF stencil object uses
//! under the static relocation model, each a 32-bit field.
//!
//! | kind | field | holds |
//! | --- | --- | --- |
//! | `PLT32`, `PC32` | a branch's displacement, or a RIP-relative operand | `S + A − P`, signed |
//! | `32` | an immediate or absolute operand | `S + A`, zero-extended |
//! | `32S` | an immediate or absolute operand | `S + A`, sign-extended |
//!
//! `S` is the hole's value — a copy's or constant's address, or an
//! immediate biased by one — `A` the relocation's addend and `P` the field's
//! own address. The compiler folds constant offsets of an operand into `A`
//! (the immediate's bias among them, `HOLE_A − 5` for a RIP-relative read of
//! `operand − 1`), so the addend is applied as the linker applies it. The
//! executable view lies below 2 GiB, so every address fits the absolute
//! forms and every displacement inside a region fits the relative one; a
//! value that does not fit is refused, never truncated.

use crate::native::Address;
use crate::native::CodeBytes;
use crate::native::PatchRefusal;
use crate::native::table::Addend;
use crate::native::table::Offset;

/// A 32-bit field's value, before its range is checked.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Field(i128);

/// A 32-bit field's little-endian bytes, ready to write.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Encoded([u8; 4]);

/// `S + A`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`PatchRefusal::FieldRange`] for an address no signed 128-bit value
/// holds, which no host has.
fn sum(
    symbol: Address,
    addend: Addend,
) -> Result<Field, PatchRefusal>
{
    let symbol = i128::try_from(symbol.0).map_err(|_overflow| PatchRefusal::FieldRange)?;
    symbol
        .checked_add(i128::from(addend.0))
        .map(Field)
        .ok_or(PatchRefusal::FieldRange)
}

/// Write `encoded` as the field at `at`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`PatchRefusal::Shape`] past the copy's end.
fn write(
    code: &mut CodeBytes<'_>,
    at: Offset,
    encoded: Encoded,
) -> Result<(), PatchRefusal>
{
    code.0
        .get_mut(at.0 .. at.0.saturating_add(4))
        .ok_or(PatchRefusal::Shape)?
        .copy_from_slice(&encoded.0);
    Ok(())
}

/// Patch the field at `at`, whose address is `site`, to `S + A − P`.
///
/// # Specification
/// - ensures: the field holds the signed displacement.
/// - executable: none — the encoding is the body's one computation; a predicate
///   would decode what it encoded.
///
/// # Errors
/// [`PatchRefusal::FieldRange`] when the displacement does not fit 32 bits.
///
/// # Adequacy
/// - hypothesis: L3 — the displacements 2³¹ − 1 forward and 2³¹ back are
///   written and read back, one byte past either is refused, and a field past
///   the copy's end is refused.
/// - witness: `native::x86_64::tests::a_relative_field_holds_exactly_32_signed_bits`
#[inline]
pub fn relative(
    code: &mut CodeBytes<'_>,
    at: Offset,
    site: Address,
    symbol: Address,
    addend: Addend,
) -> Result<(), PatchRefusal>
{
    let place = i128::try_from(site.0).map_err(|_overflow| PatchRefusal::FieldRange)?;
    let value = sum(symbol, addend)?
        .0
        .checked_sub(place)
        .ok_or(PatchRefusal::FieldRange)?;
    let field = i32::try_from(value).map_err(|_overflow| PatchRefusal::FieldRange)?;
    write(code, at, Encoded(field.to_le_bytes()))
}

/// Patch the field at `at` to `S + A`, zero-extended.
///
/// # Specification
/// - ensures: the field holds the value.
/// - executable: none — the encoding is the body's one computation; a predicate
///   would decode what it encoded.
///
/// # Errors
/// [`PatchRefusal::FieldRange`] when the value does not fit 32 unsigned
/// bits.
///
/// # Adequacy
/// - hypothesis: L3 — the values 0 and 2³² − 1, the addend applied, are written
///   and read back, and 2³² and a negative sum are refused.
/// - witness: `native::x86_64::tests::an_absolute_field_holds_exactly_its_width`
#[inline]
pub fn absolute(
    code: &mut CodeBytes<'_>,
    at: Offset,
    symbol: Address,
    addend: Addend,
) -> Result<(), PatchRefusal>
{
    let field =
        u32::try_from(sum(symbol, addend)?.0).map_err(|_overflow| PatchRefusal::FieldRange)?;
    write(code, at, Encoded(field.to_le_bytes()))
}

/// Patch the field at `at` to `S + A`, sign-extended.
///
/// # Specification
/// - ensures: the field holds the value.
/// - executable: none — the encoding is the body's one computation; a predicate
///   would decode what it encoded.
///
/// # Errors
/// [`PatchRefusal::FieldRange`] when the value does not fit 32 signed bits.
///
/// # Adequacy
/// - hypothesis: L3 — −2³¹ (by a negative addend) and 2³¹ − 1 are written and
///   read back, and 2³¹ and one below −2³¹ are refused.
/// - witness: `native::x86_64::tests::an_absolute_field_holds_exactly_its_width`
#[inline]
pub fn absolute_signed(
    code: &mut CodeBytes<'_>,
    at: Offset,
    symbol: Address,
    addend: Addend,
) -> Result<(), PatchRefusal>
{
    let field =
        i32::try_from(sum(symbol, addend)?.0).map_err(|_overflow| PatchRefusal::FieldRange)?;
    write(code, at, Encoded(field.to_le_bytes()))
}

#[cfg(test)]
mod tests
{
    use super::Encoded;
    use super::absolute;
    use super::absolute_signed;
    use super::relative;
    use crate::native::Address;
    use crate::native::CodeBytes;
    use crate::native::PatchRefusal;
    use crate::native::table::Addend;
    use crate::native::table::Offset;

    /// The field `patch` writes one byte into a five-byte copy, after a
    /// one-byte opcode.
    ///
    /// # Specification
    /// trivial.
    fn patched(
        patch: impl FnOnce(&mut CodeBytes<'_>, Offset) -> Result<(), PatchRefusal>
    ) -> Result<Encoded, PatchRefusal>
    {
        let mut bytes = [0xE9_u8, 0, 0, 0, 0];
        patch(&mut CodeBytes(&mut bytes), Offset(1))?;
        let [opcode, field @ ..] = bytes;
        assert_eq!(0xE9, opcode, "the opcode is untouched");
        Ok(Encoded(field))
    }

    /// `S + A − P` is written as a signed 32-bit field from 2³¹ − 1 forward
    /// to 2³¹ back; one byte further either way, or a field running past the
    /// copy's end, is refused.
    #[test]
    fn a_relative_field_holds_exactly_32_signed_bits()
    {
        let site = Address(0x8000_0000);
        let fits = [
            (Address(0xFFFF_FFFF), Addend(0), i32::MAX),
            (Address(0), Addend(0), i32::MIN),
            (Address(0x8000_0010), Addend(-4), 12_i32),
        ];
        for (symbol, addend, displacement) in fits {
            let field = patched(|code, at| relative(code, at, site, symbol, addend))
                .unwrap_or_else(|refusal| panic!("{symbol:?}{addend:?}: {refusal:?}"));
            assert_eq!(
                displacement,
                i32::from_le_bytes(field.0),
                "{symbol:?}{addend:?}"
            );
        }
        for (symbol, addend) in [(Address(0xFFFF_FFFF), Addend(1)), (Address(0), Addend(-1))] {
            assert_eq!(
                Err(PatchRefusal::FieldRange),
                patched(|code, at| relative(code, at, site, symbol, addend)),
                "{symbol:?}{addend:?} is refused"
            );
        }
        assert_eq!(
            Err(PatchRefusal::Shape),
            patched(|code, _at| relative(code, Offset(2), site, site, Addend(0))),
            "a field past the copy's end"
        );
    }

    /// `S + A` is written zero-extended from 0 to 2³² − 1 and sign-extended
    /// from −2³¹ to 2³¹ − 1; a value past either width is refused.
    #[test]
    fn an_absolute_field_holds_exactly_its_width()
    {
        let unsigned = [
            (Address(1), Addend(-1), 0),
            (Address(0xFFFF_FFFE), Addend(1), u32::MAX),
        ];
        for (symbol, addend, value) in unsigned {
            let field = patched(|code, at| absolute(code, at, symbol, addend))
                .unwrap_or_else(|refusal| panic!("{symbol:?}{addend:?}: {refusal:?}"));
            assert_eq!(value, u32::from_le_bytes(field.0), "{symbol:?}{addend:?}");
        }
        for (symbol, addend) in [(Address(0xFFFF_FFFF), Addend(1)), (Address(0), Addend(-1))] {
            assert_eq!(
                Err(PatchRefusal::FieldRange),
                patched(|code, at| absolute(code, at, symbol, addend)),
                "{symbol:?}{addend:?} is past 32 unsigned bits"
            );
        }
        let signed = [
            (Address(0), Addend(-0x8000_0000), i32::MIN),
            (Address(0x7FFF_FFFF), Addend(0), i32::MAX),
        ];
        for (symbol, addend, value) in signed {
            let field = patched(|code, at| absolute_signed(code, at, symbol, addend))
                .unwrap_or_else(|refusal| panic!("{symbol:?}{addend:?}: {refusal:?}"));
            assert_eq!(value, i32::from_le_bytes(field.0), "{symbol:?}{addend:?}");
        }
        for (symbol, addend) in [
            (Address(0x8000_0000), Addend(0)),
            (Address(0), Addend(-0x8000_0001)),
        ] {
            assert_eq!(
                Err(PatchRefusal::FieldRange),
                patched(|code, at| absolute_signed(code, at, symbol, addend)),
                "{symbol:?}{addend:?} is past 32 signed bits"
            );
        }
    }
}
