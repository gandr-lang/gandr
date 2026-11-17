//! The block compiler: a short block of machine code compiled from its
//! description by the `llc` of the pinned toolchain, and kept under the
//! content of that description.
//!
//! An assembly form, a system call and a foreign call each need a short block
//! of machine code under a stated convention. The convention says which
//! register takes each operand, which register gives the answer, and which
//! registers the block overwrites. A [`Description`] holds that convention as
//! data, with the target and the template.
//!
//! The compiler writes a description as one LLVM function, `block`, whose
//! body is one inline-assembly call. Its one argument is the address of the
//! operand area: one word for each operand, in the order of the operands. The
//! function loads each input from its word, makes the call, writes each output
//! to its word and returns the answer as one word, or zero. LLVM assigns the
//! registers and writes the moves. The `llc` of the pinned toolchain
//! assembles the function in a process of its own, so gandr links no LLVM.
//!
//! The bytes of a block are the text of its object. A reader of sections
//! takes them, because a binary copy of a Mach-O object is not its text. The
//! bytes run where they are copied, with no loader. So an object with a
//! relocation, an undefined symbol or a second code section is refused by
//! name.
//!
//! A [`Blocks`] keeps the bytes of each block under the digest of its
//! description, its target and its assembler: in the process, and in a
//! directory when the caller names one. A request that the process holds
//! takes no lock and allocates nothing. A request that neither holds compiles
//! one time. A second request for the same key waits for that compile and
//! starts no process. A compile that fails leaves no entry, so the next
//! request compiles again.
//!
//! # References
//!
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — design: the IO direction (§
//!   io-direction-block): one mechanism for assembly, system calls and foreign
//!   calls, and LLVM behind a process seam.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::sync::Arc;
use core::fmt;
use core::fmt::Write as _;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::PoisonError;

use object::Object as _;
use object::ObjectSection as _;
use object::ObjectSymbol as _;
use object::RelocationTarget;
use object::SectionKind;

/// The version of the lowering, in each key: a change of the lowering is a
/// change of the bytes, so it is a change of the key too.
const LOWERING: &[u8] = b"gandr block 1\0";

/// The count of temporary files that this process wrote, which makes the
/// name of each one distinct.
static WRITTEN: AtomicU64 = AtomicU64::new(0);

/// A target that a block compiles for.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Target
{
    /// `x86_64-unknown-linux-gnu`.
    LinuxX86_64,
    /// `aarch64-unknown-linux-gnu`.
    LinuxAarch64,
    /// `riscv64gc-unknown-linux-gnu`.
    LinuxRiscv64,
    /// `aarch64-apple-darwin`.
    DarwinAarch64,
}

impl Target
{
    /// Each target, in the order of the variants.
    pub const ALL: [Self; 4] = [
        Self::LinuxX86_64,
        Self::LinuxAarch64,
        Self::LinuxRiscv64,
        Self::DarwinAarch64,
    ];

    /// The name of the target in the Rust toolchain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(self) -> &'static str
    {
        match self {
            Self::LinuxX86_64 => "x86_64-unknown-linux-gnu",
            Self::LinuxAarch64 => "aarch64-unknown-linux-gnu",
            Self::LinuxRiscv64 => "riscv64gc-unknown-linux-gnu",
            Self::DarwinAarch64 => "aarch64-apple-darwin",
        }
    }

    /// The arguments that select the target in `llc`: the LLVM triple that
    /// rustc gives it, and the features of a `gc` core on riscv64.
    ///
    /// # Specification
    /// trivial.
    const fn arguments(self) -> &'static [&'static str]
    {
        match self {
            Self::LinuxX86_64 => &["-mtriple=x86_64-unknown-linux-gnu"],
            Self::LinuxAarch64 => &["-mtriple=aarch64-unknown-linux-gnu"],
            Self::LinuxRiscv64 => &[
                "-mtriple=riscv64-unknown-linux-gnu",
                "-mattr=+m,+a,+f,+d,+c",
                "-target-abi=lp64d",
            ],
            Self::DarwinAarch64 => &["-mtriple=arm64-apple-macosx11.0.0"],
        }
    }

    /// The clobbers that name the flags of the target, as Rust's `asm!`
    /// writes them. riscv64 has no flags.
    ///
    /// # Specification
    /// trivial.
    const fn flags(self) -> &'static str
    {
        match self {
            Self::LinuxX86_64 => "~{dirflag},~{fpsr},~{flags},",
            Self::LinuxAarch64 | Self::DarwinAarch64 => "~{cc},",
            Self::LinuxRiscv64 => "",
        }
    }

    /// The dialect of the template: Intel on x86-64, as Rust's `asm!` reads
    /// it, and the one dialect of each other target.
    ///
    /// # Specification
    /// trivial.
    const fn dialect(self) -> &'static str
    {
        match self {
            Self::LinuxX86_64 => " inteldialect",
            Self::LinuxAarch64 | Self::LinuxRiscv64 | Self::DarwinAarch64 => "",
        }
    }

    /// The byte that stands for the target in a key.
    ///
    /// # Specification
    /// trivial.
    const fn tag(self) -> u8
    {
        match self {
            Self::LinuxX86_64 => 0,
            Self::LinuxAarch64 => 1,
            Self::LinuxRiscv64 => 2,
            Self::DarwinAarch64 => 3,
        }
    }
}

/// The name of one register of the target, as LLVM spells it: `rax`, `x8`,
/// `a7`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Register(pub Box<str>);

impl From<&str> for Register
{
    /// trivial.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.into())
    }
}

/// A class of registers, from which LLVM picks one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Class
{
    /// A general-purpose register of the target.
    General,
}

/// Where an operand or the answer is: one named register, or a register of
/// a class.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Place
{
    /// The one register that the name gives.
    Register(Register),
    /// A register of the class.
    Class(Class),
}

/// How an operand passes between its word and its register.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Direction
{
    /// The block reads the word in the register.
    In,
    /// The block writes the register, and the word takes its value. The
    /// output can share the register of an input, as Rust's `lateout` can.
    Out,
    /// The register holds the word on entry, and the word takes the
    /// register's value on exit.
    InOut,
}

/// One operand of a block: a word of the operand area.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Operand
{
    /// How the word passes.
    pub direction: Direction,
    /// Where the word is in the block.
    pub place: Place,
}

/// The word that a block returns.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Answer
{
    /// The block returns zero.
    Zero,
    /// The block returns the value that the place holds on exit. The place
    /// can share the register of an input.
    Place(Place),
}

/// Whether the template reads or writes memory.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Memory
{
    /// The template can read and write any memory: the default.
    Clobbered,
    /// The template touches no memory, as Rust's `nomem` states.
    Untouched,
}

/// Whether the template changes the flags of the target.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Flags
{
    /// The template can change the flags: the default.
    Clobbered,
    /// The template keeps the flags, as Rust's `preserves_flags` states.
    Preserved,
}

/// The options of a block.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Options
{
    /// Whether the template touches memory.
    pub memory: Memory,
    /// Whether the template changes the flags.
    pub flags: Flags,
}

impl Options
{
    /// The options of Rust's `asm!` with no option written.
    pub const DEFAULT: Self = Self {
        memory: Memory::Clobbered,
        flags: Flags::Clobbered,
    };
}

/// The template of a block, in the syntax of Rust's `asm!`: `{0}` names the
/// register of operand 0, `{answer}` names the register of the answer, and
/// `{{` and `}}` are braces.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Template(pub Box<str>);

impl From<&str> for Template
{
    /// trivial.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &str) -> Self
    {
        Self(text.into())
    }
}

/// The description of one block: the data that the block's bytes are a
/// function of.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Description
{
    /// The target that the bytes run on.
    pub target: Target,
    /// The instructions.
    pub template: Template,
    /// The operands, one word each in this order.
    pub operands: Box<[Operand]>,
    /// The word that the block returns.
    pub answer: Answer,
    /// The registers that the template overwrites and no output names.
    pub clobbers: Box<[Register]>,
    /// The options.
    pub options: Options,
}

/// The `llc` that compiles each block.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Assembler(pub PathBuf);

impl Assembler
{
    /// The `llc` of the toolchain that built this crate, which its
    /// `llvm-tools` component holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pinned() -> Self
    {
        Self(PathBuf::from(env!("GANDR_LLC")))
    }
}

/// Where a [`Blocks`] keeps its bytes.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Cache
{
    /// In the process alone.
    Process,
    /// In the process, and in the directory for each later process.
    Directory(PathBuf),
}

/// Where the bytes of a request came from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Origin
{
    /// This request started `llc`.
    Compiled,
    /// The process held the bytes, or another request compiled them while
    /// this one waited.
    Process,
    /// The directory held the bytes.
    Directory,
}

/// The bytes of one block, and where they came from.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block
{
    /// The text of the block's object: the function `block`, entered at its
    /// first byte.
    pub bytes: Arc<[u8]>,
    /// Where this request found the bytes.
    pub origin: Origin,
}

/// Why a description gives no block.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// The assembler's file does not exist.
    Absent(PathBuf),
    /// The target has no register of the name. A name that LLVM cannot read
    /// is refused here too.
    Register(Box<str>),
    /// A reference of the template names no operand, or a brace of the
    /// template is not closed.
    Reference(Box<str>),
    /// The assembler refused the template, with the first error it wrote.
    Assembler(Box<str>),
    /// The object holds a relocation to the named symbol.
    Relocation(Box<str>),
    /// The object holds the named symbol undefined.
    Undefined(Box<str>),
    /// The object holds this count of code sections with bytes, and not one.
    Sections(usize),
    /// The assembler wrote no object that the reader parses.
    Object(Box<str>),
    /// A process or a file of the cache failed.
    Io(io::ErrorKind),
}

impl fmt::Display for Refusal
{
    /// trivial.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Absent(ref path) => write!(f, "the assembler {} is absent", path.display()),
            Self::Register(ref name) => write!(f, "the target has no register `{name}`"),
            Self::Reference(ref text) => {
                write!(f, "the template reference `{text}` names no operand")
            },
            Self::Assembler(ref error) => write!(f, "the assembler refuses the template: {error}"),
            Self::Relocation(ref symbol) => {
                write!(f, "the block holds a relocation to `{symbol}`")
            },
            Self::Undefined(ref symbol) => {
                write!(f, "the block names `{symbol}`, which it does not define")
            },
            Self::Sections(count) => write!(f, "the block has {count} code sections, and not one"),
            Self::Object(ref error) => write!(f, "the assembler's object does not parse: {error}"),
            Self::Io(kind) => write!(f, "the block's process or cache failed: {kind}"),
        }
    }
}

impl core::error::Error for Refusal
{
}

/// The key of a block: the digest of its description, its target and its
/// assembler.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Key(blake3::Hash);

/// The bytes of one key, and the lock that one compile of them holds.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Slot
{
    /// The bytes, once a request has them.
    bytes: OnceLock<Arc<[u8]>>,
    /// The lock that a request holds while it reads the directory or
    /// compiles.
    compiling: Mutex<()>,
}

/// The block compiler and the cache of its blocks.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Blocks
{
    /// The `llc` that compiles.
    assembler: Assembler,
    /// The directory that keeps each block across processes, if any.
    directory: Option<PathBuf>,
    /// The slot of each key that a request named.
    slots: papaya::HashMap<Key, Arc<Slot>>,
}

impl Blocks
{
    /// A block compiler on `assembler`, with an empty process cache.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        assembler: Assembler,
        cache: Cache,
    ) -> Self
    {
        Self {
            assembler,
            directory: match cache {
                Cache::Process => None,
                Cache::Directory(directory) => Some(directory),
            },
            slots: papaya::HashMap::new(),
        }
    }

    /// The bytes of the block that `description` describes.
    ///
    /// # Specification
    /// - ensures: the bytes are the text of the object that the assembler
    ///   writes for the lowering of `description`, the same for each request of
    ///   one key; the origin is [`Origin::Compiled`] for exactly one request of
    ///   a key that neither the process nor the directory held, and no other
    ///   request starts a process.
    /// - fails: each [`Refusal`], as its variant states. A failed request
    ///   leaves the key with no bytes.
    /// - panics: none.
    /// - executable: none — the bytes are the assembler's, observable only by
    ///   its run.
    ///
    /// # Errors
    /// The [`Refusal`] of the lowering, of the assembler, of the object or of
    /// the cache.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the system call of three arguments compiles to the
    ///   bytes that a probe ran on each host; a request that the cache holds
    ///   starts no process; each refusal is triggered and its exact variant
    ///   read.
    /// - witness: `tests::block::the_system_call_compiles_to_the_bytes_that_ran`
    /// - witness: `tests::block::a_class_operand_and_an_output_take_their_words`
    /// - witness: `tests::block::a_second_request_starts_no_process`
    /// - witness: `tests::block::requests_at_once_share_one_compile`
    /// - witness: `tests::block::each_refusal_names_its_cause`
    #[inline]
    pub fn compile(
        &self,
        description: &Description,
    ) -> Result<Block, Refusal>
    {
        let key = self.key(description);
        let slot = {
            let slots = self.slots.pin();
            if let Some(slot) = slots.get(&key)
                && let Some(bytes) = slot.bytes.get()
            {
                return Ok(Block {
                    bytes: Arc::clone(bytes),
                    origin: Origin::Process,
                });
            }
            Arc::clone(slots.get_or_insert_with(key, || Arc::new(Slot::default())))
        };
        let _compiling = slot
            .compiling
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(bytes) = slot.bytes.get() {
            return Ok(Block {
                bytes: Arc::clone(bytes),
                origin: Origin::Process,
            });
        }
        let file = self
            .directory
            .as_deref()
            .map(|directory| directory.join(key.0.to_hex().as_str()));
        let (bytes, origin) = match file.as_deref().map(fs::read) {
            Some(Ok(bytes)) => (Arc::<[u8]>::from(bytes), Origin::Directory),
            Some(Err(error)) if error.kind() != io::ErrorKind::NotFound => {
                return Err(Refusal::Io(error.kind()));
            },
            Some(Err(_)) | None => {
                let bytes = self.assemble(description)?;
                if let Some(ref file) = file {
                    keep(file, &bytes).map_err(|error| Refusal::Io(error.kind()))?;
                }
                (bytes, Origin::Compiled)
            },
        };
        Ok(Block {
            bytes: Arc::clone(slot.bytes.get_or_init(|| bytes)),
            origin,
        })
    }

    /// The key of `description` under this compiler's assembler.
    ///
    /// # Specification
    /// - ensures: two descriptions have one key exactly when they are equal, up
    ///   to the collisions of the digest.
    /// - executable: none — injectivity is a property of the encoding.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two descriptions that differ in the template alone
    ///   give two different blocks.
    /// - witness: `tests::block::a_class_operand_and_an_output_take_their_words`
    fn key(
        &self,
        description: &Description,
    ) -> Key
    {
        /// Add `count` to `hasher`, as eight bytes.
        fn counted(
            hasher: &mut blake3::Hasher,
            count: usize,
        )
        {
            hasher.update(&u64::try_from(count).unwrap_or(u64::MAX).to_le_bytes());
        }
        /// Add `bytes` to `hasher` after their length, so that no two
        /// sequences of fields give one stream.
        fn framed(
            hasher: &mut blake3::Hasher,
            bytes: &[u8],
        )
        {
            counted(hasher, bytes.len());
            hasher.update(bytes);
        }
        /// Add `place` to `hasher`.
        fn place(
            hasher: &mut blake3::Hasher,
            place: &Place,
        )
        {
            match *place {
                Place::Register(ref register) => {
                    hasher.update(&[0]);
                    framed(hasher, register.0.as_bytes());
                },
                Place::Class(Class::General) => {
                    hasher.update(&[1]);
                },
            }
        }
        let mut hasher = blake3::Hasher::new();
        hasher.update(LOWERING);
        framed(&mut hasher, self.assembler.0.as_os_str().as_encoded_bytes());
        hasher.update(&[description.target.tag()]);
        framed(&mut hasher, description.template.0.as_bytes());
        match description.answer {
            Answer::Zero => {
                hasher.update(&[0]);
            },
            Answer::Place(ref answer) => {
                hasher.update(&[1]);
                place(&mut hasher, answer);
            },
        }
        counted(&mut hasher, description.operands.len());
        for operand in &description.operands {
            let direction = match operand.direction {
                Direction::In => 0,
                Direction::Out => 1,
                Direction::InOut => 2,
            };
            hasher.update(&[direction]);
            place(&mut hasher, &operand.place);
        }
        counted(&mut hasher, description.clobbers.len());
        for clobber in &description.clobbers {
            framed(&mut hasher, clobber.0.as_bytes());
        }
        let memory = match description.options.memory {
            Memory::Clobbered => 0,
            Memory::Untouched => 1,
        };
        let flags = match description.options.flags {
            Flags::Clobbered => 0,
            Flags::Preserved => 1,
        };
        hasher.update(&[memory, flags]);
        Key(hasher.finalize())
    }

    /// Lower `description`, run the assembler on it and take the text of its
    /// object.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Blocks::compile`], less the cache.
    fn assemble(
        &self,
        description: &Description,
    ) -> Result<Arc<[u8]>, Refusal>
    {
        let module = lower(description)?;
        let mut child = Command::new(&self.assembler.0)
            .args(description.target.arguments())
            .args(["-O2", "-filetype=obj", "-o", "-", "-"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|error| {
                if error.kind() == io::ErrorKind::NotFound {
                    Refusal::Absent(self.assembler.0.clone())
                }
                else {
                    Refusal::Io(error.kind())
                }
            })?;
        let written = child
            .stdin
            .take()
            .map_or(Ok(()), |mut input| input.write_all(module.as_bytes()));
        let output = child
            .wait_with_output()
            .map_err(|error| Refusal::Io(error.kind()))?;
        if !output.status.success() {
            return Err(refusal(&String::from_utf8_lossy(&output.stderr)));
        }
        written.map_err(|error| Refusal::Io(error.kind()))?;
        text(&output.stdout)
    }
}

/// Write `bytes` to `file` whole or not at all: to a fresh file beside it,
/// then a rename over it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The first failure of the directory, the write or the rename.
fn keep(
    file: &Path,
    bytes: &[u8],
) -> io::Result<()>
{
    let directory = file.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(directory)?;
    let count = WRITTEN.fetch_add(1, Ordering::Relaxed);
    let mut name = file.as_os_str().to_owned();
    name.push(format!(".{}.{count}.part", std::process::id()));
    let part = PathBuf::from(name);
    fs::write(&part, bytes)?;
    fs::rename(&part, file).inspect_err(|_| {
        let _removed = fs::remove_file(&part);
    })
}

/// The refusal that the assembler's error text `errors` states.
///
/// # Specification
/// - ensures: [`Refusal::Register`] with the name in braces when the first
///   error is LLVM's `could not allocate … reg for constraint '{name}'`, else
///   [`Refusal::Assembler`] with the text of that first error.
/// - executable: none — the text is the assembler's.
///
/// # Adequacy
/// - hypothesis: L3 — a register that the target lacks and an instruction that
///   it lacks give their two variants with their exact text.
/// - witness: `tests::block::each_refusal_names_its_cause`
fn refusal(errors: &str) -> Refusal
{
    let first = errors
        .lines()
        .find_map(|line| line.split_once("error: ").map(|(_, error)| error))
        .unwrap_or_else(|| errors.trim());
    if first.starts_with("could not allocate")
        && let Some((_, braced)) = first.split_once("constraint '{")
        && let Some((name, _)) = braced.split_once("}'")
    {
        return Refusal::Register(name.into());
    }
    Refusal::Assembler(first.into())
}

/// The text of `object`: the bytes of its one code section.
///
/// # Specification
/// - ensures: `Ok` exactly when the object holds no relocation, no undefined
///   symbol and one code section with bytes, and then its bytes.
/// - executable: none — the object is the assembler's.
///
/// # Errors
/// [`Refusal::Relocation`], [`Refusal::Undefined`] or [`Refusal::Sections`],
/// checked in that order, or [`Refusal::Object`].
///
/// # Adequacy
/// - hypothesis: L3 — a call of a symbol, a weak symbol and a second code
///   section each give their variant with its exact name or count.
/// - witness: `tests::block::each_refusal_names_its_cause`
fn text(object: &[u8]) -> Result<Arc<[u8]>, Refusal>
{
    let unread = |error: object::Error| Refusal::Object(error.to_string().into());
    let file = object::File::parse(object).map_err(unread)?;
    for section in file.sections() {
        if let Some((_, relocation)) = section.relocations().next() {
            let symbol = if let RelocationTarget::Symbol(index) = relocation.target() {
                file.symbol_by_index(index)
                    .and_then(|symbol| symbol.name())
                    .map_err(unread)?
            }
            else {
                section.name().map_err(unread)?
            };
            return Err(Refusal::Relocation(symbol.into()));
        }
    }
    if let Some(symbol) = file.symbols().find(object::ObjectSymbol::is_undefined) {
        return Err(Refusal::Undefined(symbol.name().map_err(unread)?.into()));
    }
    let mut code = file
        .sections()
        .filter(|section| section.kind() == SectionKind::Text && section.size() > 0);
    match (code.next(), code.count()) {
        (Some(section), 0) => Ok(Arc::from(section.data().map_err(unread)?)),
        (None, _) => Err(Refusal::Sections(0)),
        (Some(_), more) => Err(Refusal::Sections(more.saturating_add(1))),
    }
}

/// The index of each operand's constraint, in the order of the operands: its
/// output for an operand that the block writes, its input for one that it
/// only reads. The answer is output 0 when the block has one.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Layout(Box<[usize]>);

impl Layout
{
    /// The index of operand `operand`'s constraint.
    ///
    /// # Specification
    /// trivial.
    fn index(
        &self,
        operand: usize,
    ) -> Option<usize>
    {
        self.0.get(operand).copied()
    }
}

/// Whether the block writes the word of an operand of `direction`.
///
/// # Specification
/// trivial.
const fn written(direction: Direction) -> bool
{
    matches!(direction, Direction::Out | Direction::InOut)
}

/// The LLVM value of the address of operand `index`'s word.
///
/// # Specification
/// trivial.
fn word(index: usize) -> String
{
    if index == 0 {
        String::from("%ops")
    }
    else {
        format!("%p{index}")
    }
}

/// The LLVM module of `description`: the function `block`.
///
/// # Specification
/// - ensures: one function `i64 @block(ptr)`, whose body loads each input word,
///   makes one inline-assembly call under the description's constraints, stores
///   each output word and returns the answer or zero. The outputs come first in
///   the order answer, written operands, clobbers, then the inputs in the order
///   read operands, tied operands.
/// - executable: none — the module is text for the assembler.
///
/// # Errors
/// [`Refusal::Register`] for a name outside `[a-z0-9]` and
/// [`Refusal::Reference`] for a reference that names no operand.
///
/// # Adequacy
/// - hypothesis: L2 — the module of the system call compiles to the bytes that
///   a probe ran, and a class operand's reference compiles to the register that
///   LLVM gave it.
/// - witness: `tests::block::the_system_call_compiles_to_the_bytes_that_ran`
/// - witness: `tests::block::a_class_operand_and_an_output_take_their_words`
fn lower(description: &Description) -> Result<String, Refusal>
{
    let operands = &description.operands;
    let answered = matches!(description.answer, Answer::Place(_));
    let outputs = usize::from(answered)
        .saturating_add(
            operands
                .iter()
                .filter(|operand| written(operand.direction))
                .count(),
        )
        .saturating_add(description.clobbers.len());
    let mut indices = Vec::with_capacity(operands.len());
    let (mut output, mut input) = (usize::from(answered), outputs);
    for operand in operands {
        let next = if written(operand.direction) {
            &mut output
        }
        else {
            &mut input
        };
        indices.push(*next);
        *next = next.saturating_add(1);
    }
    let layout = Layout(indices.into_boxed_slice());

    let mut constraints = String::new();
    let mut place = |place: &Place, prefix: &str| -> Result<(), Refusal> {
        constraints.push_str(prefix);
        match *place {
            Place::Register(ref register) => {
                named(register)?;
                constraints.push('{');
                constraints.push_str(&register.0);
                constraints.push('}');
            },
            Place::Class(Class::General) => constraints.push('r'),
        }
        constraints.push(',');
        Ok(())
    };
    if let Answer::Place(ref answer) = description.answer {
        place(answer, "=")?;
    }
    for operand in operands.iter().filter(|operand| written(operand.direction)) {
        place(&operand.place, "=")?;
    }
    // A clobber is an output that nothing reads, as Rust's `asm!` lowers it:
    // LLVM refuses an output register that the target lacks, and it ignores
    // a clobber of one.
    for clobber in &description.clobbers {
        place(&Place::Register(clobber.clone()), "=")?;
    }
    for operand in operands
        .iter()
        .filter(|operand| operand.direction == Direction::In)
    {
        place(&operand.place, "")?;
    }
    let tied: Vec<usize> = (0 .. operands.len())
        .filter(|&index| {
            operands
                .get(index)
                .is_some_and(|operand| operand.direction == Direction::InOut)
        })
        .collect();
    for &index in &tied {
        let _written = write!(constraints, "{},", layout.index(index).unwrap_or(0));
    }
    if description.options.flags == Flags::Clobbered {
        constraints.push_str(description.target.flags());
    }
    if description.options.memory == Memory::Clobbered {
        constraints.push_str("~{memory},");
    }
    let _comma = constraints.pop();

    let mut module = String::from("define i64 @block(ptr %ops) nounwind {\n");
    for (index, operand) in operands.iter().enumerate() {
        if index > 0 {
            let _written = writeln!(
                module,
                "  %p{index} = getelementptr i64, ptr %ops, i64 {index}"
            );
        }
        if operand.direction != Direction::Out {
            let _written = writeln!(
                module,
                "  %v{index} = load i64, ptr {}, align 8",
                word(index)
            );
        }
    }
    let returned = match outputs {
        0 => String::from("void"),
        1 => String::from("i64"),
        count => format!("{{ i64{} }}", ", i64".repeat(count.saturating_sub(1))),
    };
    let read = (0 .. operands.len())
        .filter(|&index| {
            operands
                .get(index)
                .is_some_and(|operand| operand.direction == Direction::In)
        })
        .chain(tied.iter().copied());
    let arguments: Vec<String> = read.map(|index| format!("i64 %v{index}")).collect();
    let call = if outputs == 0 { "call" } else { "%r = call" };
    let _written = write!(
        module,
        "  {call} {returned} asm sideeffect{} \"",
        description.target.dialect()
    );
    template(description, &layout, &mut module)?;
    let _written = writeln!(module, "\", \"{constraints}\"({})", arguments.join(", "));
    let value = |output: usize| {
        if outputs == 1 {
            String::from("%r")
        }
        else {
            format!("%o{output}")
        }
    };
    if outputs > 1 {
        for output in 0 .. outputs {
            let _written = writeln!(
                module,
                "  %o{output} = extractvalue {returned} %r, {output}"
            );
        }
    }
    for (index, operand) in operands.iter().enumerate() {
        if written(operand.direction) {
            let output = value(layout.index(index).unwrap_or(0));
            let _written = writeln!(module, "  store i64 {output}, ptr {}, align 8", word(index));
        }
    }
    let answer = if answered {
        value(0)
    }
    else {
        String::from("0")
    };
    let _written = writeln!(module, "  ret i64 {answer}\n}}");
    Ok(module)
}

/// Refuse a register name that LLVM cannot read between braces.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Register`] for an empty name or a name outside `[a-z0-9]`.
fn named(register: &Register) -> Result<(), Refusal>
{
    let readable = !register.0.is_empty()
        && register
            .0
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit());
    if readable {
        Ok(())
    }
    else {
        Err(Refusal::Register(register.0.clone()))
    }
}

/// Write the template of `description` into `module` as the body of an LLVM
/// string: each reference as LLVM's `${n}`, each `$` doubled, and each byte
/// that the string cannot hold as `\XX`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Reference`] for a reference that names no operand, a brace
/// that is not closed, or `{answer}` in a block that answers zero.
fn template(
    description: &Description,
    layout: &Layout,
    module: &mut String,
) -> Result<(), Refusal>
{
    let text = &description.template.0;
    let mut rest = text.as_ref();
    let mut lowered = String::with_capacity(text.len());
    while let Some(at) = rest.find(['{', '}', '$']) {
        let (before, from) = rest.split_at(at);
        lowered.push_str(before);
        if let Some(after) = from.strip_prefix("{{") {
            lowered.push('{');
            rest = after;
        }
        else if let Some(after) = from.strip_prefix("}}") {
            lowered.push('}');
            rest = after;
        }
        else if let Some(after) = from.strip_prefix('$') {
            lowered.push_str("$$");
            rest = after;
        }
        else if let Some(inner) = from.strip_prefix('{')
            && let Some((name, after)) = inner.split_once('}')
        {
            let index = if name == "answer" {
                matches!(description.answer, Answer::Place(_)).then_some(0)
            }
            else {
                name.parse::<usize>()
                    .ok()
                    .and_then(|operand| layout.index(operand))
            };
            let Some(index) = index
            else {
                return Err(Refusal::Reference(name.into()));
            };
            let _written = write!(lowered, "${{{index}}}");
            rest = after;
        }
        else {
            return Err(Refusal::Reference(from.into()));
        }
    }
    lowered.push_str(rest);
    for byte in lowered.bytes() {
        if byte == b' ' || (byte.is_ascii_graphic() && byte != b'"' && byte != b'\\') {
            module.push(char::from(byte));
        }
        else {
            let _written = write!(module, "\\{byte:02X}");
        }
    }
    Ok(())
}
