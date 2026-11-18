//! The arm64 patcher: the three relocation kinds the Mach-O and ELF stencil
//! objects use, applied to a copied stencil, with the GOT load relaxed away.
//!
//! On `aarch64-apple-darwin` every operand hole arrives as a GOT load — an
//! `adrp` (`GOT_LOAD_PAGE21`) and an `ldr` (`GOT_LOAD_PAGEOFF12`) of the
//! hole's slot — whatever the relocation or code model: Mach-O has no
//! absolute-immediate relocation for arm64. `aarch64-unknown-linux-gnu`
//! under the default position-independent model emits the same pair as
//! `ADR_GOT_PAGE` and `LD64_GOT_LO12_NC`, and its continuations as `JUMP26`,
//! so the build script maps both objects onto these three kinds. The emitter
//! needs no GOT: it knows each operand when it copies, so it rewrites each
//! half in place, as a linker relaxes a GOT load to a symbol it can see. The
//! build script refused any `ldr` whose base and target registers differ, so
//! each half rewrites one register:
//!
//! | operand | `adrp` becomes | `ldr` becomes |
//! | --- | --- | --- |
//! | an immediate below 2¹⁶ | `movz x, #v` | `nop` |
//! | an immediate below 2³² | `movz x, #lo` | `movk x, #hi, lsl #16` |
//! | an address within ±4 GiB | `adrp x, page(v)` | `add x, x, pageoff(v)` |
//!
//! A continuation is a `b` (`BRANCH26`, ±128 MiB) patched to its target; a
//! region is smaller than that reach.

use crate::native::Address;
use crate::native::CodeBytes;
use crate::native::PatchRefusal;
use crate::native::Value;
use crate::native::table::Offset;

/// One instruction word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Encoding(u32);

/// `nop`.
const NOP: u32 = 0xD503_201F;
/// `movz x0, #0`.
const MOVZ: u32 = 0xD280_0000;
/// `movk x0, #0, lsl #16`.
const MOVK_16: u32 = 0xF2A0_0000;
/// `adrp x0, 0`.
const ADRP: u32 = 0x9000_0000;
/// The bits that identify an `adrp`.
const ADRP_MASK: u32 = 0x9F00_0000;
/// `ldr x0, [x0, #0]`, unsigned offset.
const LDR: u32 = 0xF940_0000;
/// The bits that identify a 64-bit unsigned-offset `ldr`.
const LDR_MASK: u32 = 0xFFC0_0000;
/// `add x0, x0, #0`.
const ADD_IMMEDIATE: u32 = 0x9100_0000;
/// `b 0`.
const BRANCH: u32 = 0x1400_0000;
/// A register field's bits.
const REGISTER: u32 = 0x1F;
/// A `b`'s reach either side of it: 2²⁷ bytes.
const BRANCH_REACH: i128 = 0x0800_0000;
/// An `adrp`'s reach either side of it: 2²⁰ pages.
const PAGE_REACH: i128 = 0x0010_0000;

/// Read the instruction at `at`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`PatchRefusal::Shape`] past the copy's end.
fn read(
    code: &CodeBytes<'_>,
    at: Offset,
) -> Result<Encoding, PatchRefusal>
{
    let bytes = code
        .0
        .get(at.0 .. at.0.saturating_add(4))
        .and_then(|word| <[u8; 4]>::try_from(word).ok())
        .ok_or(PatchRefusal::Shape)?;
    Ok(Encoding(u32::from_le_bytes(bytes)))
}

/// Write `instruction` at `at`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`PatchRefusal::Shape`] past the copy's end.
fn write(
    code: &mut CodeBytes<'_>,
    at: Offset,
    instruction: Encoding,
) -> Result<(), PatchRefusal>
{
    code.0
        .get_mut(at.0 .. at.0.saturating_add(4))
        .ok_or(PatchRefusal::Shape)?
        .copy_from_slice(&instruction.0.to_le_bytes());
    Ok(())
}

/// The signed distance from `from` to `to`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`PatchRefusal::BranchRange`] for an address no signed 128-bit value
/// holds, which no host has.
fn distance(
    from: Address,
    to: Address,
) -> Result<Distance, PatchRefusal>
{
    let from = i128::try_from(from.0).map_err(|_overflow| PatchRefusal::BranchRange)?;
    let to = i128::try_from(to.0).map_err(|_overflow| PatchRefusal::BranchRange)?;
    to.checked_sub(from)
        .map(Distance)
        .ok_or(PatchRefusal::BranchRange)
}

/// A signed byte or page distance.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Distance(i128);

/// Patch the `b` at `at` (address `pc`) to branch to `target`.
///
/// # Specification
/// - ensures: the instruction is `b target`.
/// - executable: none — the encoding is the body's one computation; a predicate
///   would decode what it encoded.
///
/// # Errors
/// [`PatchRefusal::BranchRange`] past ±128 MiB or off a word boundary.
///
/// # Adequacy
/// - hypothesis: L3 — the farthest target either side encodes and decodes back,
///   and one word further and a target off a word boundary are refused; every
///   named program then runs native through these branches.
/// - witness: `native::aarch64::tests::a_branch_reaches_exactly_its_range`
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub fn branch(
    code: &mut CodeBytes<'_>,
    at: Offset,
    pc: Address,
    target: Address,
) -> Result<(), PatchRefusal>
{
    let delta = distance(pc, target)?.0;
    if delta < BRANCH_REACH.saturating_neg() || delta >= BRANCH_REACH || delta & 3 != 0 {
        return Err(PatchRefusal::BranchRange);
    }
    let words = u32::try_from(delta.wrapping_shr(2) & 0x03FF_FFFF)
        .map_err(|_overflow| PatchRefusal::BranchRange)?;
    write(code, at, Encoding(BRANCH | words))
}

/// The register a GOT load half writes, when the half has the shape
/// `expected` under `mask`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`PatchRefusal::Shape`] otherwise.
fn register(
    instruction: Encoding,
    mask: Encoding,
    expected: Encoding,
) -> Result<Encoding, PatchRefusal>
{
    if instruction.0 & mask.0 == expected.0 {
        Ok(Encoding(instruction.0 & REGISTER))
    }
    else {
        Err(PatchRefusal::Shape)
    }
}

/// Rewrite the `adrp` half of a GOT load at `at` (address `pc`) to begin
/// materialising `value` in its register.
///
/// # Specification
/// - ensures: an immediate's low half by `movz`, or an address's page by
///   `adrp`.
/// - executable: none — the encoding is the body's one computation; a predicate
///   would decode what it encoded.
///
/// # Errors
/// [`PatchRefusal::Shape`] for a site that is not an `adrp`;
/// [`PatchRefusal::FieldRange`] for an immediate at or past 2³²;
/// [`PatchRefusal::PageRange`] for an address past ±4 GiB.
///
/// # Adequacy
/// - hypothesis: L3 — an immediate and an address are materialised into the
///   `adrp`'s own register and read back; an immediate of 2³², the farthest
///   page past reach and a site that is not an `adrp` are refused.
/// - witness: `native::aarch64::tests::a_got_pair_materialises_its_operand`
/// - witness: `native::aarch64::tests::a_got_pair_refuses_what_it_cannot_reach`
#[inline]
pub fn page(
    code: &mut CodeBytes<'_>,
    at: Offset,
    pc: Address,
    value: Value,
) -> Result<(), PatchRefusal>
{
    let target = register(read(code, at)?, Encoding(ADRP_MASK), Encoding(ADRP))?.0;
    let instruction = match value {
        Value::Immediate(word) => {
            let value =
                u32::try_from(usize::from(word)).map_err(|_overflow| PatchRefusal::FieldRange)?;
            MOVZ | (value & 0xFFFF).wrapping_shl(5) | target
        },
        Value::Address(address) => {
            let pages = distance(
                Address(pc.0.wrapping_shr(12)),
                Address(address.0.wrapping_shr(12)),
            )?
            .0;
            if pages < PAGE_REACH.saturating_neg() || pages >= PAGE_REACH {
                return Err(PatchRefusal::PageRange);
            }
            let bits =
                u32::try_from(pages & 0x1F_FFFF).map_err(|_overflow| PatchRefusal::PageRange)?;
            ADRP | (bits & 0x3).wrapping_shl(29)
                | (bits.wrapping_shr(2) & 0x7_FFFF).wrapping_shl(5)
                | target
        },
    };
    write(code, at, Encoding(instruction))
}

/// Rewrite the `ldr` half of a GOT load at `at` to finish materialising
/// `value` in its register.
///
/// # Specification
/// - ensures: an immediate's high half by `movk` (a `nop` when it is zero), or
///   an address's page offset by `add`.
/// - executable: none — the encoding is the body's one computation; a predicate
///   would decode what it encoded.
///
/// # Errors
/// [`PatchRefusal::Shape`] for a site that is not the `ldr` over one
/// register; [`PatchRefusal::FieldRange`] for an immediate at or past 2³².
///
/// # Adequacy
/// - hypothesis: L3 — an immediate's high half, a zero high half and an
///   address's page offset are written over the `ldr`'s register; an `ldr` over
///   two registers is refused.
/// - witness: `native::aarch64::tests::a_got_pair_materialises_its_operand`
/// - witness: `native::aarch64::tests::a_got_pair_refuses_what_it_cannot_reach`
#[inline]
pub fn page_offset(
    code: &mut CodeBytes<'_>,
    at: Offset,
    value: Value,
) -> Result<(), PatchRefusal>
{
    let instruction = read(code, at)?;
    let target = register(instruction, Encoding(LDR_MASK), Encoding(LDR))?.0;
    if instruction.0.wrapping_shr(5) & REGISTER != target {
        return Err(PatchRefusal::Shape);
    }
    let rewritten = match value {
        Value::Immediate(word) => {
            let value =
                u32::try_from(usize::from(word)).map_err(|_overflow| PatchRefusal::FieldRange)?;
            let high = value.wrapping_shr(16);
            if high == 0 {
                NOP
            }
            else {
                MOVK_16 | high.wrapping_shl(5) | target
            }
        },
        Value::Address(address) => {
            let offset =
                u32::try_from(address.0 & 0xFFF).map_err(|_overflow| PatchRefusal::PageRange)?;
            ADD_IMMEDIATE | offset.wrapping_shl(10) | target.wrapping_shl(5) | target
        },
    };
    write(code, at, Encoding(rewritten))
}

#[cfg(test)]
mod tests
{
    use gandr_runtime_stencils::Word;

    use super::ADRP;
    use super::BRANCH;
    use super::Encoding;
    use super::NOP;
    use super::branch;
    use super::page;
    use super::page_offset;
    use crate::native::Address;
    use crate::native::CodeBytes;
    use crate::native::PatchRefusal;
    use crate::native::Value;
    use crate::native::table::Offset;

    /// Where the patched instruction sits.
    const PC: Address = Address(0x1_0000_0000);
    /// `adrp x5, 0`.
    const ADRP_X5: Encoding = Encoding(0x9000_0005);
    /// `ldr x5, [x5, #0]`.
    const LDR_X5: Encoding = Encoding(0xF940_00A5);
    /// `ldr x5, [x6, #0]`: base and target differ.
    const LDR_X5_X6: Encoding = Encoding(0xF940_00C5);

    /// The word `patch` leaves over the four bytes of `instruction`.
    ///
    /// # Specification
    /// trivial.
    fn patched(
        instruction: Encoding,
        patch: impl FnOnce(&mut CodeBytes<'_>) -> Result<(), PatchRefusal>,
    ) -> Result<Encoding, PatchRefusal>
    {
        let mut bytes = instruction.0.to_le_bytes();
        patch(&mut CodeBytes(&mut bytes))?;
        Ok(Encoding(u32::from_le_bytes(bytes)))
    }

    /// A `b` reaches 2²⁷ − 4 bytes forward and 2²⁷ back, and decodes to
    /// the distance it was given; one word past either end, or a distance
    /// off a word boundary, is refused.
    #[test]
    fn a_branch_reaches_exactly_its_range()
    {
        let from_pc = |delta: isize| Address(PC.0.wrapping_add_signed(delta));
        let decode = |word: Encoding| -> isize {
            let field = isize::try_from(word.0 & 0x03FF_FFFF).expect("26 bits");
            let signed = if field >= 0x0200_0000 {
                field.wrapping_sub(0x0400_0000)
            }
            else {
                field
            };
            signed.wrapping_mul(4)
        };
        for delta in [0x07FF_FFFC_isize, -0x0800_0000, 4, -4] {
            let word = patched(Encoding(BRANCH), |code| {
                branch(code, Offset(0), PC, from_pc(delta))
            })
            .unwrap_or_else(|refusal| panic!("{delta:#x}: {refusal:?}"));
            assert_eq!(BRANCH, word.0 & 0xFC00_0000, "{delta:#x}: still a `b`");
            assert_eq!(delta, decode(word), "{delta:#x}: decodes to its distance");
        }
        for delta in [0x0800_0000_isize, -0x0800_0004, 2] {
            assert_eq!(
                Err(PatchRefusal::BranchRange),
                patched(Encoding(BRANCH), |code| branch(
                    code,
                    Offset(0),
                    PC,
                    from_pc(delta)
                )),
                "{delta:#x} is refused"
            );
        }
    }

    /// An immediate below 2³² becomes `movz`/`movk` into the load's own
    /// register, its high half a `nop` when zero; an address becomes
    /// `adrp`/`add` to its page and offset.
    #[test]
    fn a_got_pair_materialises_its_operand()
    {
        let wide = Value::Immediate(Word::from(0x1234_5678_usize));
        assert_eq!(
            Ok(Encoding(0xD28A_CF05)),
            patched(ADRP_X5, |code| page(code, Offset(0), PC, wide)),
            "the low half by `movz x5, #0x5678`"
        );
        assert_eq!(
            Ok(Encoding(0xF2A2_4685)),
            patched(LDR_X5, |code| page_offset(code, Offset(0), wide)),
            "the high half by `movk x5, #0x1234, lsl #16`"
        );
        let narrow = Value::Immediate(Word::from(0xFFFF_usize));
        assert_eq!(
            Ok(Encoding(NOP)),
            patched(LDR_X5, |code| page_offset(code, Offset(0), narrow)),
            "no high half, no instruction"
        );
        let address = Value::Address(Address(0x1_0003_4567));
        assert_eq!(
            Ok(Encoding(ADRP | 0x0000_01A5)),
            patched(ADRP_X5, |code| page(code, Offset(0), PC, address)),
            "`adrp x5` 0x34 pages forward: immlo 0, immhi 0xD"
        );
        assert_eq!(
            Ok(Encoding(0x9115_9CA5)),
            patched(LDR_X5, |code| page_offset(code, Offset(0), address)),
            "the page offset by `add x5, x5, #0x567`"
        );
    }

    /// An immediate of 2³², a page past the `adrp`'s reach, a site that is
    /// not an `adrp`, and an `ldr` whose base is another register are each
    /// refused by name.
    #[test]
    fn a_got_pair_refuses_what_it_cannot_reach()
    {
        let too_wide = Value::Immediate(Word::from(0x1_0000_0000_usize));
        assert_eq!(
            Err(PatchRefusal::FieldRange),
            patched(ADRP_X5, |code| page(code, Offset(0), PC, too_wide)),
            "2³² has no `movz`/`movk` pair"
        );
        let far = Value::Address(Address(0x2_0000_0000));
        assert_eq!(
            Err(PatchRefusal::PageRange),
            patched(ADRP_X5, |code| page(code, Offset(0), PC, far)),
            "2²⁰ pages is past reach"
        );
        let narrow = Value::Immediate(Word::from(1_usize));
        assert_eq!(
            Err(PatchRefusal::Shape),
            patched(Encoding(NOP), |code| page(code, Offset(0), PC, narrow)),
            "a `nop` is not an `adrp`"
        );
        assert_eq!(
            Err(PatchRefusal::Shape),
            patched(LDR_X5_X6, |code| page_offset(code, Offset(0), narrow)),
            "an `ldr` over two registers"
        );
    }
}
