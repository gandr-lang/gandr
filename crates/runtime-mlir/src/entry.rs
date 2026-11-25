//! The entry of a program with no libc, and the machine block of the exit
//! system call.
//!
//! [`Entry`] prints two functions of the `llvm` dialect. The machine block
//! `gandr.exit` is one inline assembly operation: the system call `exit_group`
//! of Linux x86-64, number 231, with the code in `rdi`. It does not return.
//! The call `exit` (60) ends only the calling thread. A write of `io_uring` to
//! a regular file can start a worker thread of the kernel in the process. Then
//! the status of the process is not the code. `exit_group` ends each thread
//! with the code. The entry [`ENTRY`] calls the main definition under
//! `tailcc`, widens its word to 64 bits, and gives it to `gandr.exit`. So an
//! object of a module with its entry links into an executable with no libc and
//! no start file.
//!
//! Each symbol that the lowering makes, and that is not a definition, has a
//! dot in its name. The name of a definition of gandr has none. So a
//! definition named `exit` or `_start` meets no symbol of the entry. The link
//! names the entry with its option, because the entry is not `_start`.
//! The block `gandr.exit` has the internal linkage. So [`ENTRY`] is the one
//! global symbol of the entry.
//!
//! # Boundaries
//!
//! The kernel enters the entry with the stack aligned to 16 bytes, and with no
//! return address. A function expects one return address on the stack. So
//! the entry aligns its stack again, by the attribute `alignstack`. The exit
//! code is the low 8 bits of the word of main, as the kernel reads it.
//!
//! # References
//!
//! - `vault:01a21222-e4bd-74a7-82be-989aaccefe85` — dependency: §
//!   seam-changes-library, the entry of a program against the trunk.

use core::fmt;

use gandr_kernel_term::IntegerWidth;

use crate::lower::Symbol;

/// The symbol of the entry of a program. The link names it as the entry.
pub const ENTRY: &str = "gandr.start";

/// The entry of a program and its machine block of exit, for one main
/// definition with no parameter.
///
/// # Specification
/// - ensures: the value names a function of a lowered module that takes no
///   parameter, and the width of its result.
/// - panics: none.
/// - executable: none — a type-level block: a data declaration has no body and
///   no call boundary to check.
///
/// # Adequacy
/// - hypothesis: L3 — the object of the fixture with its entry links with the
///   `lld` of the pin, and the executable exits with the answer of main.
/// - witness: `lower::tests::an_object_with_the_entry_links_and_exits_with_the_answer`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Entry<'name>
{
    /// The function that the entry calls.
    main: Symbol<'name>,
    /// The width of its result.
    result: IntegerWidth,
}

impl<'name> Entry<'name>
{
    /// The entry of `main`, whose result has the width `result`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        main: Symbol<'name>,
        result: IntegerWidth,
    ) -> Self
    {
        Self { main, result }
    }
}

impl fmt::Display for Entry<'_>
{
    /// The machine block `gandr.exit` and the entry [`ENTRY`], as MLIR text.
    ///
    /// # Specification
    /// - ensures: `gandr.exit` with one inline assembly operation and no
    ///   return, then [`ENTRY`] with a `tailcc` call of main, a widening to 64
    ///   bits below that width, and a call of `gandr.exit`.
    /// - fails: an error of `f`.
    /// - panics: none.
    /// - executable: none — a clause over the written text would print the
    ///   functions a second time.
    ///
    /// # Errors
    ///
    /// An error of the formatter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the text compiles with the module of the fixture, the
    ///   object links, and the executable exits with the answer `4` of main.
    /// - witness: `lower::tests::an_object_with_the_entry_links_and_exits_with_the_answer`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(concat!(
            "llvm.func internal @gandr.exit(%code: i64) {\n",
            "  %number = llvm.mlir.constant(231 : i64) : i64\n",
            "  %unused = llvm.inline_asm has_side_effects \"syscall\", ",
            "\"={rax},{rax},{rdi},~{rcx},~{r11},~{memory}\" %number, %code : (i64, i64) -> i64\n",
            "  llvm.unreachable\n",
            "}\n",
        ))?;
        writeln!(
            f,
            "llvm.func @{ENTRY}() attributes {{passthrough = [[\"alignstack\", \"16\"]]}} {{"
        )?;
        let bits = u32::from(self.result.bits());
        writeln!(
            f,
            "  %answer = llvm.call tailcc @{}() : () -> i{bits}",
            self.main
        )?;
        let code = if bits < 64 {
            writeln!(f, "  %code = llvm.zext %answer : i{bits} to i64")?;
            "%code"
        }
        else {
            "%answer"
        };
        writeln!(f, "  llvm.call @gandr.exit({code}) : (i64) -> ()")?;
        f.write_str("  llvm.unreachable\n}\n")
    }
}
