//! Native emission: a lowered function's instructions copied stencil by
//! stencil into an executable region and patched in place.
//!
//! Emission is two passes over the instruction list — each copy's offset,
//! then copy and patch — and one write of the function's constants after its
//! code. A copy's `hole_next` is the copy after it, so a stencil ending in
//! the branch to `hole_next` is copied without it. Each region begins with
//! its shared copies: the halt the sentinel frame resumes, the three exits
//! every exhaustion hole branches to, and the two frame stubs. A region is
//! never larger than a branch reaches, so every continuation and exit is in
//! range of every copy in it; a full region is followed by a fresh one with
//! its own shared copies, and the code already emitted stays where it is.

#[cfg(any(target_arch = "aarch64", test))]
mod aarch64;
mod memory;
mod table;
#[cfg(any(target_arch = "x86_64", test))]
mod x86_64;

use gandr_runtime_stencils::StencilId;
use gandr_runtime_stencils::Word;

use crate::function::Alt;
use crate::function::Constant;
use crate::function::Function;
use crate::function::Instruction;
use crate::function::Label;
use crate::function::Operand;
use crate::function::Stub;
pub use crate::native::memory::MapFailure;
use crate::native::memory::Region;
use crate::native::table::HoleKind;
use crate::native::table::HoleSymbol;
use crate::native::table::Offset;
use crate::native::table::code;

/// The bytes one region maps: within a branch's reach on both patchers.
const REGION_BYTES: usize = 1 << 26;

/// An absolute address in the process's address space.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Address(pub usize);

/// The writable bytes of code being copied and patched.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Debug)]
pub struct CodeBytes<'bytes>(pub &'bytes mut [u8]);

/// What a hole is patched to.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Value
{
    /// An immediate, already biased by one as the stencil expects.
    Immediate(Word),
    /// The address of a copy, a stub, an exit or a constant.
    Address(Address),
}

/// Why a hole could not be patched.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PatchRefusal
{
    /// A branch target lies beyond the branch's reach.
    BranchRange,
    /// An address lies beyond the page reach of an `adrp`.
    PageRange,
    /// A value does not fit the 32-bit field or the 32-bit immediate.
    FieldRange,
    /// The site is not the instruction shape the hole's kind rewrites.
    Shape,
    /// A hole names an operand where its kind patches a branch, or the
    /// reverse.
    Kind,
}

/// Why emission failed.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EmitRefusal
{
    /// Mapping a region failed.
    Map(MapFailure),
    /// The function is larger than a region.
    Oversized,
    /// A hole could not be patched.
    Patch(PatchRefusal),
    /// A label an instruction names is unbound.
    Unbound(Label),
    /// The last instruction continues past the function's end.
    FallsOff,
    /// An instruction reads a second continuation it lacks, or an operand it
    /// was not given.
    Operand,
}

/// The shared copies at a region's start.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Shared
{
    /// `stencil_halt`, the sentinel frame's code.
    halt: Address,
    /// `stencil_heap_exhausted`.
    heap: Address,
    /// `stencil_frames_exhausted`.
    frames: Address,
    /// `stencil_fuel_exhausted`.
    fuel: Address,
    /// `stencil_stuck`.
    stuck: Address,
    /// Each of [`Stub::ALL`], in its order.
    stubs: [Address; Stub::ALL.len()],
}

/// An emitted function: where it starts, where each label landed, and the
/// halt and stubs of its region.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Emitted
{
    /// The entry: the first instruction's copy.
    pub entry: Word,
    /// Each label's code address, by label index; zero for a label never
    /// bound.
    pub labels: Vec<Word>,
    /// The halt the sentinel frame resumes.
    pub halt: Word,
    /// Each of [`Stub::ALL`]'s shared copy, in its order.
    pub stubs: [Word; Stub::ALL.len()],
}

/// The executable regions emitted code lives in.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub struct Native
{
    /// Every region mapped, the last the one emitted into; earlier regions
    /// hold code a cache still serves.
    regions: Vec<(Region, Shared)>,
    /// Each instruction's offset in the function being emitted, reused.
    offsets: Vec<Offset>,
}

/// The shared copies, in layout order: the exits, then each of
/// [`Stub::ALL`].
const SHARED: [StencilId; 5_usize.wrapping_add(Stub::ALL.len())] = [
    StencilId::Halt,
    StencilId::HeapExhausted,
    StencilId::FramesExhausted,
    StencilId::FuelExhausted,
    StencilId::Stuck,
    Stub::Apply.stencil(),
    Stub::Force.stencil(),
    Stub::Argument.stencil(),
    Stub::Reset.stencil(),
    Stub::Answer.stencil(),
];

impl Native
{
    /// Emit `function`, mapping a region first when none has room.
    ///
    /// # Specification
    /// - requires: `function` came from the lowering, so every label it names
    ///   is bound and its last instruction does not continue at `hole_next`.
    /// - ensures: the copy at `entry` runs the function: each instruction's
    ///   stencil with its operands, continuing at the next copy or its label,
    ///   its exits at its region's shared copies.
    /// - executable: none — running the function is observed only by running
    ///   it.
    ///
    /// # Errors
    /// [`EmitRefusal`] naming why.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program emits its function here and
    ///   compares the answer with the executor's and the L machine's.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    #[inline]
    pub fn emit(
        &mut self,
        function: &Function,
    ) -> Result<Emitted, EmitRefusal>
    {
        let instructions = function.instructions();
        if let Some(last) = instructions.last()
            && code(last.stencil).holes.iter().any(|hole| {
                hole.symbol == HoleSymbol::Next && hole.offset.0 < copied(last.stencil).0
            })
        {
            return Err(EmitRefusal::FallsOff);
        }
        let mut offsets = core::mem::take(&mut self.offsets);
        offsets.clear();
        let mut length = 0_usize;
        for instruction in instructions {
            offsets.push(Offset(length));
            length = length.saturating_add(copied(instruction.stencil).0);
        }
        offsets.push(Offset(length));
        let data = Offset(length.next_multiple_of(8));
        let total = Offset(
            data.0
                .saturating_add(function.constants().len().saturating_mul(8)),
        );
        if total.0.saturating_add(shared_bytes().0) > REGION_BYTES {
            self.offsets = offsets;
            return Err(EmitRefusal::Oversized);
        }
        let result = self.place(function, &offsets, data, total);
        self.offsets = offsets;
        result
    }

    /// Reserve `total` bytes in a region with room, then copy, patch and lay
    /// out `function` there.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::emit`].
    fn place(
        &mut self,
        function: &Function,
        offsets: &[Offset],
        data: Offset,
        total: Offset,
    ) -> Result<Emitted, EmitRefusal>
    {
        let reserved = self
            .regions
            .last_mut()
            .and_then(|&mut (ref mut region, _)| region.reserve(total).ok());
        let reservation = if let Some(reservation) = reserved {
            reservation
        }
        else {
            self.map()?;
            let &mut (ref mut region, _) = self.regions.last_mut().ok_or(EmitRefusal::Oversized)?;
            region
                .reserve(total)
                .map_err(|_full| EmitRefusal::Oversized)?
        };
        let &mut (ref mut region, shared) =
            self.regions.last_mut().ok_or(EmitRefusal::Oversized)?;
        let base = region.address(reservation);
        let at = |index: usize| -> Address {
            Address(
                base.0
                    .wrapping_add(offsets.get(index).map_or(0, |offset| offset.0)),
            )
        };
        let label = |target: Label| -> Result<Address, EmitRefusal> {
            function
                .target(target)
                .map(|position| at(position.0))
                .map_err(|_unbound| EmitRefusal::Unbound(target))
        };
        let constant = |offset: Constant| -> Address {
            Address(
                base.0
                    .wrapping_add(data.0)
                    .wrapping_add(usize::from(offset).saturating_mul(8)),
            )
        };
        region.write(
            reservation,
            |bytes: CodeBytes<'_>| -> Result<(), EmitRefusal> {
                for (index, instruction) in function.instructions().iter().enumerate() {
                    let start = offsets.get(index).map_or(0, |offset| offset.0);
                    let end = offsets
                        .get(index.saturating_add(1))
                        .map_or(start, |offset| offset.0);
                    let mut copy = CodeBytes(
                        bytes
                            .0
                            .get_mut(start .. end)
                            .ok_or(EmitRefusal::Oversized)?,
                    );
                    let next = at(index.saturating_add(1));
                    copy_and_patch(&mut copy, at(index), instruction, &|symbol, operand| {
                        resolve(
                            symbol,
                            operand,
                            instruction,
                            next,
                            shared,
                            &label,
                            &constant,
                        )
                    })?;
                }
                for (slot, word) in function.constants().iter().enumerate() {
                    let start = data.0.saturating_add(slot.saturating_mul(8));
                    let target = bytes
                        .0
                        .get_mut(start .. start.saturating_add(8))
                        .ok_or(EmitRefusal::Oversized)?;
                    target.copy_from_slice(&usize::from(*word).to_le_bytes());
                }
                Ok(())
            },
        )?;
        let labels = function
            .labels()
            .map(|target| label(target).map_or(Word::ZERO, |address| Word::from(address.0)))
            .collect();
        Ok(Emitted {
            entry: Word::from(base.0),
            labels,
            halt: Word::from(shared.halt.0),
            stubs: shared.stubs.map(|address| Word::from(address.0)),
        })
    }

    /// Map a fresh region and copy its shared stencils in.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`EmitRefusal::Map`] when the mapping fails, or a patch refusal for a
    /// shared copy.
    fn map(&mut self) -> Result<(), EmitRefusal>
    {
        let mut region = Region::map(Offset(REGION_BYTES)).map_err(EmitRefusal::Map)?;
        let reservation = region
            .reserve(shared_bytes())
            .map_err(|_full| EmitRefusal::Oversized)?;
        let base = region.address(reservation);
        let mut addresses = [Address(0); SHARED.len()];
        let mut start = 0_usize;
        for (address, stencil) in addresses.iter_mut().zip(SHARED) {
            *address = Address(base.0.wrapping_add(start));
            start = start.saturating_add(code(stencil).bytes.len());
        }
        let [
            halt,
            heap,
            frames,
            fuel,
            stuck,
            apply,
            force,
            argument,
            reset,
            answer,
        ] = addresses;
        let shared = Shared {
            halt,
            heap,
            frames,
            fuel,
            stuck,
            stubs: [apply, force, argument, reset, answer],
        };
        region.write(
            reservation,
            |bytes: CodeBytes<'_>| -> Result<(), EmitRefusal> {
                let mut start = 0_usize;
                for (&address, stencil) in addresses.iter().zip(SHARED) {
                    let whole = code(stencil).bytes.len();
                    let mut copy = CodeBytes(
                        bytes
                            .0
                            .get_mut(start .. start.saturating_add(whole))
                            .ok_or(EmitRefusal::Oversized)?,
                    );
                    let instruction = Instruction {
                        stencil,
                        a: Operand::Unused,
                        b: Operand::Unused,
                        alt: Alt::None,
                    };
                    copy_and_patch(&mut copy, address, &instruction, &|symbol, _operand| {
                        match symbol {
                            HoleSymbol::HeapExhausted => Ok(Value::Address(shared.heap)),
                            HoleSymbol::FramesExhausted => Ok(Value::Address(shared.frames)),
                            HoleSymbol::FuelExhausted => Ok(Value::Address(shared.fuel)),
                            HoleSymbol::Stuck => Ok(Value::Address(shared.stuck)),
                            HoleSymbol::Next | HoleSymbol::Alt | HoleSymbol::A | HoleSymbol::B => {
                                Err(EmitRefusal::Operand)
                            },
                        }
                    })?;
                    start = start.saturating_add(whole);
                }
                Ok(())
            },
        )?;
        self.regions.push((region, shared));
        Ok(())
    }
}

/// The bytes the shared copies take at a region's start.
///
/// # Specification
/// trivial.
fn shared_bytes() -> Offset
{
    Offset(
        SHARED
            .iter()
            .map(|&stencil| code(stencil).bytes.len())
            .fold(0_usize, usize::saturating_add),
    )
}

/// The bytes a copy of `stencil` takes when its continuation is the next
/// copy: its code without the droppable tail.
///
/// # Specification
/// trivial.
fn copied(stencil: StencilId) -> Offset
{
    let stencil = code(stencil);
    Offset(stencil.bytes.len().saturating_sub(stencil.tail.0))
}

/// The value a hole of `symbol` in `instruction` is patched to.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`EmitRefusal::Operand`] for a continuation or operand the instruction
/// lacks, or [`EmitRefusal::Unbound`] for an unbound label.
fn resolve<L, C>(
    symbol: HoleSymbol,
    operand: Operand,
    instruction: &Instruction,
    next: Address,
    shared: Shared,
    label: &L,
    constant: &C,
) -> Result<Value, EmitRefusal>
where
    L: Fn(Label) -> Result<Address, EmitRefusal>,
    C: Fn(Constant) -> Address,
{
    Ok(match symbol {
        HoleSymbol::Next => Value::Address(next),
        HoleSymbol::Alt => match instruction.alt {
            Alt::At(target) => Value::Address(label(target)?),
            Alt::None => return Err(EmitRefusal::Operand),
        },
        HoleSymbol::HeapExhausted => Value::Address(shared.heap),
        HoleSymbol::FramesExhausted => Value::Address(shared.frames),
        HoleSymbol::FuelExhausted => Value::Address(shared.fuel),
        HoleSymbol::Stuck => Value::Address(shared.stuck),
        HoleSymbol::A | HoleSymbol::B => match operand {
            // An immediate is patched biased by one, which the stencil
            // subtracts: a static's address is never null, and the compiler
            // assumes it.
            Operand::Immediate(immediate) => {
                Value::Immediate(Word::from(usize::from(immediate).saturating_add(1)))
            },
            Operand::Code(target) => Value::Address(label(target)?),
            Operand::Data(offset) => Value::Address(constant(offset)),
            Operand::Stub(stub) => Value::Address(stub.of(&shared.stubs)),
            Operand::Unused => return Err(EmitRefusal::Operand),
        },
    })
}

/// Copy `instruction`'s stencil into `copy` — as many bytes as the copy
/// holds, so a copy shorter by the droppable tail drops it — and patch every
/// hole inside what was copied.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As the patcher and `resolve`.
fn copy_and_patch<R>(
    copy: &mut CodeBytes<'_>,
    pc: Address,
    instruction: &Instruction,
    resolve: &R,
) -> Result<(), EmitRefusal>
where
    R: Fn(HoleSymbol, Operand) -> Result<Value, EmitRefusal>,
{
    let stencil = code(instruction.stencil);
    let length = copy.0.len();
    let source = stencil.bytes.get(.. length).ok_or(EmitRefusal::Oversized)?;
    copy.0.copy_from_slice(source);
    for hole in stencil.holes {
        if hole.offset.0 >= length {
            continue;
        }
        let operand = match hole.symbol {
            HoleSymbol::A => instruction.a,
            HoleSymbol::B => instruction.b,
            HoleSymbol::Next
            | HoleSymbol::Alt
            | HoleSymbol::HeapExhausted
            | HoleSymbol::FramesExhausted
            | HoleSymbol::FuelExhausted
            | HoleSymbol::Stuck => Operand::Unused,
        };
        let value = resolve(hole.symbol, operand)?;
        let site = Address(pc.0.wrapping_add(hole.offset.0));
        patch(copy, hole.offset, site, hole.kind, value).map_err(EmitRefusal::Patch)?;
    }
    Ok(())
}

/// Apply one relocation of `kind` at `offset` of `copy`, whose address is
/// `site`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The patcher's [`PatchRefusal`].
#[cfg(target_arch = "aarch64")]
fn patch(
    copy: &mut CodeBytes<'_>,
    offset: Offset,
    site: Address,
    kind: HoleKind,
    value: Value,
) -> Result<(), PatchRefusal>
{
    match (kind, value) {
        (HoleKind::Branch26, Value::Address(target)) => aarch64::branch(copy, offset, site, target),
        (HoleKind::Page21, _) => aarch64::page(copy, offset, site, value),
        (HoleKind::PageOff12, _) => aarch64::page_offset(copy, offset, value),
        (HoleKind::Branch26, Value::Immediate(_)) => Err(PatchRefusal::Kind),
    }
}

/// Apply one relocation of `kind` at `offset` of `copy`, whose address is
/// `site`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The patcher's [`PatchRefusal`].
#[cfg(target_arch = "x86_64")]
fn patch(
    copy: &mut CodeBytes<'_>,
    offset: Offset,
    site: Address,
    kind: HoleKind,
    value: Value,
) -> Result<(), PatchRefusal>
{
    let symbol = match value {
        Value::Immediate(word) => Address(usize::from(word)),
        Value::Address(address) => address,
    };
    match kind {
        HoleKind::Relative32(addend) => x86_64::relative(copy, offset, site, symbol, addend),
        HoleKind::Absolute32(addend) => x86_64::absolute(copy, offset, symbol, addend),
        HoleKind::Absolute32Signed(addend) => x86_64::absolute_signed(copy, offset, symbol, addend),
    }
}
