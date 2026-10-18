//! The generator: compile the stencil crate to an object for the target,
//! read each stencil's bytes and relocations out of it, and write the table
//! the patcher copies from.
//!
//! The generator refuses an object it cannot patch, naming what it met: a
//! relocation to anything but a hole, a relocation kind outside the patcher's
//! set for the target, a section other than code and unwind metadata with
//! bytes in it, a defined code symbol that is not a stencil (a helper the
//! compiler did not inline), a stencil of no bytes (two stencils the compiler
//! merged), and a stencil set that differs from `StencilId::ALL`. A stencil
//! that grows a `memcpy` call, a jump table or a constant pool fails the build
//! rather than the run.
//!
//! A target without a patcher — anything but arm64 on macOS or Linux and
//! Linux x86-64 — compiles no object and writes an empty table: its runs take
//! the portable executor.

use core::fmt::Write as _;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitStatus;

use gandr_runtime_stencils::StencilId;
use object::Object as _;
use object::ObjectSection as _;
use object::ObjectSymbol as _;
use object::RelocationFlags;
use object::RelocationTarget;
use object::SectionIndex;
use object::SymbolKind;

/// Why the generator refused the stencil object.
#[derive(Debug)]
enum Refusal
{
    /// Cargo did not set a variable every build script receives.
    Environment(&'static str),
    /// Reading or writing a file failed.
    Io(std::io::Error),
    /// The stencil crate did not compile.
    Compile(ExitStatus),
    /// The object did not parse.
    Object(object::Error),
    /// Writing the table text failed.
    Format(core::fmt::Error),
    /// A section with bytes the patcher does not copy.
    Section(String),
    /// A defined code symbol that is not a stencil.
    Helper(String),
    /// A stencil `StencilId::ALL` names and the object lacks.
    Missing(String),
    /// A `stencil_*` symbol `StencilId::ALL` does not name.
    Extra(String),
    /// A stencil of no bytes: the compiler merged it with an identical one.
    Merged(String),
    /// A relocation outside the patcher's set, with where and why.
    Relocation(String),
}

impl core::fmt::Display for Refusal
{
    /// The refusal, for the build log.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Environment(name) => write!(f, "cargo did not set {name}"),
            Self::Io(ref error) => write!(f, "file access failed: {error}"),
            Self::Compile(status) => write!(f, "the stencil crate did not compile: {status}"),
            Self::Object(ref error) => write!(f, "the stencil object did not parse: {error}"),
            Self::Format(error) => write!(f, "the table text did not format: {error}"),
            Self::Section(ref name) => {
                write!(
                    f,
                    "the stencils need section {name}, which the patcher does not copy"
                )
            },
            Self::Helper(ref name) => write!(f, "{name} is code no stencil inlined"),
            Self::Missing(ref name) => write!(f, "the object lacks {name}"),
            Self::Extra(ref name) => write!(f, "{name} is not in the executor's stencil list"),
            Self::Merged(ref name) => {
                write!(
                    f,
                    "{name} has no bytes of its own: merged with an identical stencil"
                )
            },
            Self::Relocation(ref detail) => write!(f, "{detail}"),
        }
    }
}

impl From<std::io::Error> for Refusal
{
    /// The I/O failure.
    ///
    /// # Specification
    /// trivial.
    fn from(error: std::io::Error) -> Self
    {
        Self::Io(error)
    }
}

impl From<object::Error> for Refusal
{
    /// The parse failure.
    ///
    /// # Specification
    /// trivial.
    fn from(error: object::Error) -> Self
    {
        Self::Object(error)
    }
}

impl From<core::fmt::Error> for Refusal
{
    /// The formatting failure.
    ///
    /// # Specification
    /// trivial.
    fn from(error: core::fmt::Error) -> Self
    {
        Self::Format(error)
    }
}

/// The three object layouts a patcher exists for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Layout
{
    /// `aarch64-apple-darwin`: one `__text` section, `_`-prefixed symbols,
    /// `BRANCH26` and `GOT_LOAD` pairs.
    MachOArm64,
    /// `aarch64-unknown-linux-gnu`, the default position-independent model:
    /// one section per function, `JUMP26` branches and `ADR_GOT_PAGE` /
    /// `LD64_GOT_LO12_NC` pairs — Mach-O's three kinds under ELF's names, so
    /// one arm64 patcher takes both.
    ElfArm64,
    /// `x86_64-unknown-linux-gnu`, static relocation model: one section per
    /// function, `PLT32` branches and absolute or PC-relative operands.
    ElfX86_64,
}

/// One stencil read from the object.
#[derive(Debug)]
struct Read
{
    /// The symbol, without the platform prefix.
    name: String,
    /// Its section.
    section: SectionIndex,
    /// Its first byte's offset in the section.
    start: u64,
    /// Its bytes.
    bytes: Vec<u8>,
    /// Its holes: offset, kind expression, symbol variant.
    holes: Vec<(u64, String, &'static str)>,
    /// The bytes of the trailing branch to `hole_next` a copy drops.
    tail: Tail,
}

/// A count of trailing bytes a copy drops.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Tail(usize);

/// The hole symbols, without the platform prefix, and the variant each
/// becomes in the table.
const HOLES: [(&str, &str); 8] = [
    ("hole_next", "Next"),
    ("hole_alt", "Alt"),
    ("hole_heap_exhausted", "HeapExhausted"),
    ("hole_frames_exhausted", "FramesExhausted"),
    ("hole_fuel_exhausted", "FuelExhausted"),
    ("hole_stuck", "Stuck"),
    ("HOLE_A", "A"),
    ("HOLE_B", "B"),
];

/// Sections the patcher never copies, whose bytes are allowed: unwind
/// tables, the compiler's notes and the symbol tables.
const SKIPPED: [&str; 9] = [
    "__compact_unwind",
    "__eh_frame",
    ".eh_frame",
    ".comment",
    ".note.GNU-stack",
    ".llvm_addrsig",
    ".symtab",
    ".strtab",
    ".shstrtab",
];

/// Generate the stencil table.
///
/// # Specification
/// - ensures: `$OUT_DIR/stencils.rs` holds one static per stencil of
///   `StencilId::ALL` with its bytes, its holes and its droppable tail, and the
///   `code` lookup over them; empty on a target without a patcher.
/// - executable: none — the table's correctness is what the emitted code does,
///   observable only by running it.
///
/// # Errors
/// A [`Refusal`] naming the first refusal the module documentation lists.
///
/// # Adequacy
/// - hypothesis: L2 — every named program runs from the table this writes,
///   native, and is compared with the answer it states; a wrong byte, hole or
///   tail changes an answer or crashes the run.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
fn main() -> Result<(), Refusal>
{
    let variable = |name: &'static str| env::var_os(name).ok_or(Refusal::Environment(name));
    let manifest = PathBuf::from(variable("CARGO_MANIFEST_DIR")?);
    let out = PathBuf::from(variable("OUT_DIR")?);
    let table = out.join("stencils.rs");
    println!("cargo::rerun-if-changed=../runtime-stencils/src");
    println!("cargo::rustc-check-cfg=cfg(gandr_patcher)");
    let os = variable("CARGO_CFG_TARGET_OS")?;
    let arch = variable("CARGO_CFG_TARGET_ARCH")?;
    let layout = match (os.to_str(), arch.to_str()) {
        (Some("macos"), Some("aarch64")) => Layout::MachOArm64,
        (Some("linux"), Some("aarch64")) => Layout::ElfArm64,
        (Some("linux"), Some("x86_64")) => Layout::ElfX86_64,
        _ => {
            fs::write(
                &table,
                "// No patcher for this target: runs take the portable executor.\n",
            )?;
            return Ok(());
        },
    };
    println!("cargo::rustc-cfg=gandr_patcher");
    let object_path = out.join("stencils.o");
    let rustc = env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc"));
    let mut command = Command::new(rustc);
    command
        .args([
            "--edition",
            "2024",
            "--crate-type",
            "lib",
            "--crate-name",
            "gandr_runtime_stencils",
            "--emit=obj",
            "--cap-lints",
            "allow",
            "--cfg",
            "gandr_stencil_object",
            "-C",
            "opt-level=3",
            "-C",
            "panic=abort",
            "-C",
            "debuginfo=0",
            "-C",
            "debug-assertions=off",
            "-C",
            "overflow-checks=off",
            "--target",
        ])
        .arg(variable("TARGET")?);
    if layout == Layout::ElfX86_64 {
        command.args(["-C", "relocation-model=static"]);
    }
    let status = command
        .arg("-o")
        .arg(&object_path)
        .arg(manifest.join("../runtime-stencils/src/lib.rs"))
        .status()?;
    if !status.success() {
        return Err(Refusal::Compile(status));
    }
    let data = fs::read(&object_path)?;
    let file = object::File::parse(&*data)?;
    let prefix = match layout {
        Layout::MachOArm64 => "_",
        Layout::ElfArm64 | Layout::ElfX86_64 => "",
    };

    for section in file.sections() {
        let name = section.name()?;
        let skipped = SKIPPED.contains(&name)
            || name.starts_with(".rela")
            || section.kind() == object::SectionKind::Text;
        if section.size() > 0 && !skipped {
            return Err(Refusal::Section(name.to_owned()));
        }
    }

    let mut read: Vec<Read> = Vec::new();
    for symbol in file.symbols() {
        let Some(section) = symbol.section_index()
        else {
            continue;
        };
        if symbol.kind() != SymbolKind::Text {
            continue;
        }
        let full = symbol.name()?;
        let bare = full.strip_prefix(prefix).unwrap_or(full);
        if full.starts_with("ltmp") {
            continue;
        }
        if !bare.starts_with("stencil_") {
            return Err(Refusal::Helper(full.to_owned()));
        }
        let base = file.section_by_index(section)?.address();
        let start = symbol
            .address()
            .checked_sub(base)
            .ok_or_else(|| Refusal::Helper(full.to_owned()))?;
        read.push(Read {
            name: bare.to_owned(),
            section,
            start,
            bytes: Vec::new(),
            holes: Vec::new(),
            tail: Tail(0),
        });
    }
    read.sort_by_key(|stencil| (stencil.section.0, stencil.start));
    let ends: Vec<u64> = read
        .iter()
        .enumerate()
        .map(|(position, stencil)| {
            let next = position.checked_add(1).and_then(|after| read.get(after));
            match next {
                Some(following) if following.section == stencil.section => Ok(following.start),
                _ => file
                    .section_by_index(stencil.section)
                    .map(|section| section.size()),
            }
        })
        .collect::<Result<_, _>>()?;
    for (stencil, &end) in read.iter_mut().zip(&ends) {
        let section = file.section_by_index(stencil.section)?;
        let code = section.data()?;
        let span = usize::try_from(stencil.start)
            .ok()
            .zip(usize::try_from(end).ok())
            .and_then(|(from, to)| code.get(from .. to))
            .ok_or_else(|| Refusal::Merged(stencil.name.clone()))?;
        if span.is_empty() {
            return Err(Refusal::Merged(stencil.name.clone()));
        }
        stencil.bytes = span.to_vec();
    }

    for section in file.sections() {
        if section.kind() != object::SectionKind::Text {
            continue;
        }
        for (offset, relocation) in section.relocations() {
            let at = |why: &str| {
                Refusal::Relocation(format!(
                    "{why} at {offset:#x} in {}",
                    section.name().unwrap_or("?")
                ))
            };
            let RelocationTarget::Symbol(index) = relocation.target()
            else {
                return Err(at("a relocation naming no symbol"));
            };
            let target = file.symbol_by_index(index)?.name()?;
            let bare = target.strip_prefix(prefix).unwrap_or(target);
            let Some(&(_, symbol)) = HOLES.iter().find(|&&(hole, _)| hole == bare)
            else {
                return Err(at(&format!("a relocation naming {target}, not a hole")));
            };
            let continuation = !matches!(symbol, "A" | "B");
            let kind = match (layout, relocation.flags()) {
                (Layout::MachOArm64, RelocationFlags::MachO { r_type, .. }) => match r_type {
                    object::macho::ARM64_RELOC_BRANCH26 if continuation => {
                        String::from("HoleKind::Branch26")
                    },
                    object::macho::ARM64_RELOC_GOT_LOAD_PAGE21 if !continuation => {
                        String::from("HoleKind::Page21")
                    },
                    object::macho::ARM64_RELOC_GOT_LOAD_PAGEOFF12 if !continuation => {
                        String::from("HoleKind::PageOff12")
                    },
                    _ => return Err(at(&format!("Mach-O relocation kind {r_type} on {bare}"))),
                },
                (Layout::ElfArm64, RelocationFlags::Elf { r_type }) => {
                    if relocation.addend() != 0 {
                        return Err(at(&format!(
                            "ELF relocation kind {r_type} on {bare} with addend {}",
                            relocation.addend()
                        )));
                    }
                    match r_type {
                        object::elf::R_AARCH64_JUMP26 if continuation => {
                            String::from("HoleKind::Branch26")
                        },
                        object::elf::R_AARCH64_ADR_GOT_PAGE if !continuation => {
                            String::from("HoleKind::Page21")
                        },
                        object::elf::R_AARCH64_LD64_GOT_LO12_NC if !continuation => {
                            String::from("HoleKind::PageOff12")
                        },
                        _ => return Err(at(&format!("ELF relocation kind {r_type} on {bare}"))),
                    }
                },
                (Layout::ElfX86_64, RelocationFlags::Elf { r_type }) => {
                    let addend = relocation.addend();
                    match r_type {
                        object::elf::R_X86_64_PLT32 | object::elf::R_X86_64_PC32 => {
                            format!("HoleKind::Relative32(Addend({addend}))")
                        },
                        object::elf::R_X86_64_32 if !continuation => {
                            format!("HoleKind::Absolute32(Addend({addend}))")
                        },
                        object::elf::R_X86_64_32S if !continuation => {
                            format!("HoleKind::Absolute32Signed(Addend({addend}))")
                        },
                        _ => return Err(at(&format!("ELF relocation kind {r_type} on {bare}"))),
                    }
                },
                (Layout::MachOArm64 | Layout::ElfArm64 | Layout::ElfX86_64, _) => {
                    return Err(at("a relocation in another object format's flags"));
                },
            };
            let owner = read
                .iter_mut()
                .rev()
                .find(|stencil| stencil.section == section.index() && stencil.start <= offset)
                .ok_or_else(|| at("a relocation outside every stencil"))?;
            let inside = offset
                .checked_sub(owner.start)
                .ok_or_else(|| at("a relocation before its stencil"))?;
            owner.holes.push((inside, kind, symbol));
        }
    }

    for stencil in &mut read {
        stencil.holes.sort_unstable();
        if layout != Layout::ElfX86_64 {
            check_got_pairs(stencil)?;
        }
        stencil.tail = droppable_tail(layout, stencil);
    }

    for id in StencilId::ALL {
        let name = id.symbol();
        if !read.iter().any(|stencil| stencil.name == name.as_ref()) {
            return Err(Refusal::Missing(name.as_ref().to_owned()));
        }
    }
    if let Some(extra) = read.iter().find(|stencil| {
        !StencilId::ALL
            .iter()
            .any(|id| id.symbol().as_ref() == stencil.name)
    }) {
        return Err(Refusal::Extra(extra.name.clone()));
    }

    let mut text = String::from("// Generated by the build script from the stencil object.\n");
    for stencil in &read {
        let upper = stencil.name.to_ascii_uppercase();
        writeln!(text, "/// `{}`'s code.", stencil.name)?;
        writeln!(text, "static {upper}: StencilCode = StencilCode {{")?;
        write!(text, "    bytes: &[")?;
        for byte in &stencil.bytes {
            write!(text, "{byte}, ")?;
        }
        writeln!(text, "],")?;
        writeln!(text, "    holes: &[")?;
        for &(offset, ref kind, symbol) in &stencil.holes {
            writeln!(
                text,
                "        Hole {{ offset: Offset({offset}), kind: {kind}, symbol: HoleSymbol::{symbol} }},"
            )?;
        }
        writeln!(text, "    ],")?;
        writeln!(text, "    tail: Offset({}),", stencil.tail.0)?;
        writeln!(text, "}};")?;
    }
    writeln!(text, "/// The code of `stencil`, copied before patching.")?;
    writeln!(text, "///")?;
    writeln!(text, "/// # Specification")?;
    writeln!(text, "/// trivial.")?;
    writeln!(text, "#[must_use]")?;
    writeln!(
        text,
        "pub const fn code(stencil: StencilId) -> &'static StencilCode"
    )?;
    writeln!(text, "{{")?;
    writeln!(text, "    match stencil {{")?;
    for id in StencilId::ALL {
        let name = id.symbol();
        let stem = name
            .as_ref()
            .strip_prefix("stencil_")
            .unwrap_or_else(|| name.as_ref());
        let variant: String = stem
            .split('_')
            .flat_map(|word| {
                let mut letters = word.chars();
                letters
                    .next()
                    .map(|first| first.to_ascii_uppercase())
                    .into_iter()
                    .chain(letters)
            })
            .collect();
        writeln!(
            text,
            "        StencilId::{variant} => &{},",
            name.as_ref().to_ascii_uppercase()
        )?;
    }
    writeln!(text, "    }}")?;
    writeln!(text, "}}")?;
    fs::write(&table, text)?;
    Ok(())
}

/// Refuse a `GOT_LOAD` pair the patcher cannot rewrite: each `PAGE21` site
/// an `adrp`, each `PAGEOFF12` site a 64-bit `ldr` whose base and target
/// register are one register, so the pair can become `movz`/`movk` or
/// `adrp`/`add` over that register.
///
/// # Specification
/// - ensures: `Ok` exactly when every operand hole of `stencil` has that shape.
/// - executable: none — the shape is a property of the instruction bytes the
///   decoder reads; restating it as a predicate would repeat the body.
///
/// # Errors
/// [`Refusal::Relocation`] naming the first site of another shape.
///
/// # Adequacy
/// - hypothesis: L2 — every stencil passes this check before the named programs
///   run native on arm64; a pair the relaxation could not rewrite would compute
///   a wrong address and change an answer.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
fn check_got_pairs(stencil: &Read) -> Result<(), Refusal>
{
    for &(offset, ref kind, _) in &stencil.holes {
        let word = usize::try_from(offset)
            .ok()
            .and_then(|at| stencil.bytes.get(at .. at.checked_add(4)?))
            .and_then(|bytes| <[u8; 4]>::try_from(bytes).ok())
            .map(u32::from_le_bytes)
            .ok_or_else(|| {
                Refusal::Relocation(format!("{} at {offset:#x}: no instruction", stencil.name))
            })?;
        let shaped = match kind.as_str() {
            "HoleKind::Page21" => word & 0x9F00_0000 == 0x9000_0000,
            "HoleKind::PageOff12" => {
                word & 0xFFC0_0000 == 0xF940_0000 && word & 0x1F == word.wrapping_shr(5) & 0x1F
            },
            _ => true,
        };
        if !shaped {
            return Err(Refusal::Relocation(format!(
                "{} at {offset:#x}: {word:#010x} is not the GOT load shape the patcher rewrites",
                stencil.name
            )));
        }
    }
    Ok(())
}

/// The bytes a copy of `stencil` followed by its `hole_next` continuation
/// drops: the trailing unconditional branch to that continuation, when the
/// stencil ends in one.
///
/// # Specification
/// - ensures: 4 for an arm64 `b` and 5 for an x86-64 `jmp rel32` whose
///   displacement is the last hole, a `hole_next`; 0 otherwise.
/// - executable: none — the branch's encoding is the decoder's to read; a
///   predicate would repeat the body.
///
/// # Adequacy
/// - hypothesis: L2 — every named program runs native from copies placed end to
///   end with their tails dropped; a wrong count leaves a branch to nowhere or
///   cuts an instruction, and the run changes or crashes.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
fn droppable_tail(
    layout: Layout,
    stencil: &Read,
) -> Tail
{
    let length = stencil.bytes.len();
    let Some(&(offset, _, symbol)) = stencil.holes.last()
    else {
        return Tail(0);
    };
    let last = length.checked_sub(4).and_then(|at| u64::try_from(at).ok());
    if symbol != "Next" || last != Some(offset) {
        return Tail(0);
    }
    Tail(match layout {
        Layout::MachOArm64 | Layout::ElfArm64 => {
            let word = length
                .checked_sub(4)
                .and_then(|at| stencil.bytes.get(at ..))
                .and_then(|bytes| <[u8; 4]>::try_from(bytes).ok())
                .map(u32::from_le_bytes);
            if word.is_some_and(|instruction| instruction & 0xFC00_0000 == 0x1400_0000) {
                4
            }
            else {
                0
            }
        },
        Layout::ElfX86_64 => {
            let opcode = length.checked_sub(5).and_then(|at| stencil.bytes.get(at));
            if opcode == Some(&0xE9) { 5 } else { 0 }
        },
    })
}
