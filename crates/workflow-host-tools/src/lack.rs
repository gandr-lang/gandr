//! The tools that a host lacks, read from mise's listing of a checkout.
//!
//! `mise ls --current --json` lists each tool of a checkout with its version,
//! its install state and its install path. A tool lacks in three cases: mise
//! holds no install of it, its install path holds no program, or one of its
//! programs is an ELF file of another machine. A tool whose backend needs a
//! tool that the host disables stays out: the host runs none of it, as the
//! tools of `npm:` where `node` is off.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use std::io::Read as _;
use std::path::Path;

use anodized::spec;
use serde::Deserialize;

use crate::error::HostToolsError;
use crate::names::Json;
use crate::names::Platform;
use crate::names::ToolKey;
use crate::names::Version;

/// The tool that each backend needs to install a tool of it.
const BACKEND_NEEDS: [(&str, &str); 5] = [
    ("npm", "node"),
    ("cargo", "rust"),
    ("go", "go"),
    ("pipx", "python"),
    ("gem", "ruby"),
];

/// The machine of an ELF file, as the `e_machine` field of its header names
/// it.
///
/// # Specification
/// - provides: the machine that a program runs on, compared with the host's.
/// - executable: none — a plain record.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Machine(u16);

impl Machine
{
    /// 64-bit ARM.
    pub const AARCH64: Self = Self(183);
    /// 32-bit ARM.
    pub const ARM: Self = Self(40);
    /// 32-bit x86.
    pub const I386: Self = Self(3);
    /// 64-bit PowerPC.
    pub const PPC64: Self = Self(21);
    /// RISC-V.
    pub const RISCV: Self = Self(243);
    /// 64-bit x86.
    pub const X86_64: Self = Self(62);

    /// The machine that this program runs on, or none for an architecture
    /// that no host of ours runs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn host() -> Option<Self>
    {
        match std::env::consts::ARCH {
            "aarch64" => Some(Self::AARCH64),
            "riscv64" => Some(Self::RISCV),
            "x86_64" => Some(Self::X86_64),
            _ => None,
        }
    }
}

impl fmt::Display for Machine
{
    /// Writes the machine's name, or its number when it has none here.
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
            Self::AARCH64 => f.write_str("aarch64"),
            Self::ARM => f.write_str("arm"),
            Self::I386 => f.write_str("i386"),
            Self::PPC64 => f.write_str("ppc64"),
            Self::RISCV => f.write_str("riscv64"),
            Self::X86_64 => f.write_str("x86-64"),
            Self(number) => write!(f, "machine {number}"),
        }
    }
}

impl Platform
{
    /// The platform of this program: its system and its architecture, as Rust
    /// names them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn host() -> Self
    {
        Self::from(format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH).as_str())
    }
}

/// One tool of mise's listing at one version.
///
/// # Specification
/// - provides: the version, whether mise holds an install of it, and the
///   install's path.
/// - executable: none — a plain record.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct Entry
{
    /// The version.
    pub version: Version,
    /// Whether mise holds an install of the tool at the version.
    pub installed: bool,
    /// The install's path, as mise prints it.
    pub install_path: String,
}

/// mise's listing of a checkout's tools, `mise ls --current --json`.
///
/// # Specification
/// - provides: each tool of the checkout with its versions.
/// - executable: none — [`Listing::read`] fills it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Listing(BTreeMap<ToolKey, Vec<Entry>>);

impl Listing
{
    /// Read mise's listing from `json`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each tool of `json` stands with its entries.
    /// - provides: the reading of `mise ls --current --json`.
    /// - fails: [`HostToolsError::Listing`] when `json` is no listing of mise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a listing of three tools reads whole.
    /// - witness: `lack::tests::a_tool_whose_backend_needs_a_disabled_tool_stays_out`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Listing { .. })))]
    #[inline]
    pub fn read(json: &Json) -> Result<Self, HostToolsError>
    {
        serde_json::from_str(json.as_ref())
            .map(Self)
            .map_err(|error| HostToolsError::Listing {
                message: error.to_string(),
            })
    }
}

/// The tools that the host disables, read from `json`, the output of `mise
/// settings get disable_tools`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each tool of the JSON list `json` stands, in its order.
/// - provides: the tools whose backends the check leaves out.
/// - fails: [`HostToolsError::Listing`] when `json` is no list of names.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a list of one tool and an empty list read whole.
/// - witness: `lack::tests::a_tool_whose_backend_needs_a_disabled_tool_stays_out`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Listing { .. })))]
#[inline]
pub fn disabled(json: &Json) -> Result<Vec<ToolKey>, HostToolsError>
{
    serde_json::from_str(json.as_ref()).map_err(|error| HostToolsError::Listing {
        message: error.to_string(),
    })
}

/// A tool that a host lacks.
///
/// # Specification
/// - provides: the tool, its version, and why the host lacks it.
/// - executable: none — a plain record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Lack
{
    /// mise holds no install of the tool.
    Absent
    {
        /// The tool.
        tool: ToolKey,
        /// Its version.
        version: Version,
    },
    /// The install's path holds no program.
    Empty
    {
        /// The tool.
        tool: ToolKey,
        /// Its version.
        version: Version,
    },
    /// A program of the install is an ELF file of another machine.
    Foreign
    {
        /// The tool.
        tool: ToolKey,
        /// Its version.
        version: Version,
        /// The program's machine.
        machine: Machine,
    },
}

impl fmt::Display for Lack
{
    /// Writes the lack as the second half of the check's line: `lacks <tool>
    /// <version>`, or `holds <tool> <version> for <machine>`.
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
            Self::Absent {
                ref tool,
                ref version,
            } => write!(f, "lacks {tool} {version}"),
            Self::Empty {
                ref tool,
                ref version,
            } => write!(f, "lacks {tool} {version}: its install holds no program"),
            Self::Foreign {
                ref tool,
                ref version,
                machine,
            } => write!(f, "holds {tool} {version} for {machine}"),
        }
    }
}

/// What an install's path holds.
///
/// # Specification
/// - provides: whether the install holds no program, a program of another
///   machine, or only programs that fit the host.
/// - executable: none — a plain record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Inspection
{
    /// The install holds no program.
    Empty,
    /// A program of the install is an ELF file of this other machine.
    Foreign(Machine),
    /// The install holds a program, and none of another machine.
    Fit,
}

/// The tools of `listing` that the host lacks, in the listing's order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each tool whose backend needs a tool of `disabled` stays out.
///   Each other entry gives [`Lack::Absent`] when mise holds no install of it,
///   [`Lack::Empty`] when [`inspect`] finds no program in its install, and
///   [`Lack::Foreign`] when [`inspect`] finds a program of another machine than
///   `host`.
/// - provides: the refusal's reading of a host.
/// - fails: every refusal of [`inspect`].
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — an absent tool, a tool of a disabled backend, an install
///   of another machine and an empty install each give their verdict.
/// - witness: `lack::tests::a_tool_whose_backend_needs_a_disabled_tool_stays_out`
/// - witness: `lack::tests::an_install_of_another_machine_and_an_empty_install_lack`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Io { .. })))]
#[inline]
pub fn lacks(
    listing: &Listing,
    disabled: &[ToolKey],
    host: Option<Machine>,
) -> Result<Vec<Lack>, HostToolsError>
{
    let skipped: BTreeSet<&str> = BACKEND_NEEDS
        .iter()
        .filter(|&&(_, needed)| disabled.iter().any(|tool| *tool == *needed))
        .map(|&(backend, _)| backend)
        .collect();
    let mut found = Vec::new();
    for (tool, entries) in &listing.0 {
        let text: &str = tool.as_ref();
        if text
            .split_once(':')
            .is_some_and(|(backend, _)| skipped.contains(backend))
        {
            continue;
        }
        for entry in entries {
            let lack = if entry.installed {
                match inspect(Path::new(&entry.install_path), host)? {
                    Inspection::Fit => None,
                    Inspection::Empty => Some(Lack::Empty {
                        tool: tool.clone(),
                        version: entry.version.clone(),
                    }),
                    Inspection::Foreign(machine) => Some(Lack::Foreign {
                        tool: tool.clone(),
                        version: entry.version.clone(),
                        machine,
                    }),
                }
            }
            else {
                Some(Lack::Absent {
                    tool: tool.clone(),
                    version: entry.version.clone(),
                })
            };
            found.extend(lack);
        }
    }
    Ok(found)
}

/// What the install at `root` holds: each file with an execute bit under
/// it, a shared library aside, is a program.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Inspection::Foreign`] when a program of `root` is an ELF file
///   whose machine is not `host`; else [`Inspection::Empty`] when no program
///   stands under `root`; else [`Inspection::Fit`]. A `root` that does not
///   stand is empty. The walk follows no link to a directory, and a file whose
///   name holds `.so` is a shared library.
/// - provides: the reading of one install.
/// - fails: [`HostToolsError::Io`] when a directory under `root` cannot be
///   read.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a program of another machine, a script, and an install
///   with no program each give their verdict.
/// - witness: `lack::tests::an_install_of_another_machine_and_an_empty_install_lack`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Io { .. })))]
#[inline]
pub fn inspect(
    root: &Path,
    host: Option<Machine>,
) -> Result<Inspection, HostToolsError>
{
    use std::os::unix::fs::PermissionsExt as _;
    let io = |path: &Path, error: &std::io::Error| HostToolsError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    };
    if !root.is_dir() {
        return Ok(Inspection::Empty);
    }
    let mut programs = false;
    let mut directories = vec![root.to_path_buf()];
    while let Some(directory) = directories.pop() {
        let entries = std::fs::read_dir(&directory).map_err(|error| io(&directory, &error))?;
        for entry in entries {
            let entry = entry.map_err(|error| io(&directory, &error))?;
            let path = entry.path();
            let kind = entry.file_type().map_err(|error| io(&path, &error))?;
            if kind.is_dir() {
                directories.push(path);
                continue;
            }
            // A link to a directory leads out of the install, or back into it.
            let Ok(metadata) = std::fs::metadata(&path)
            else {
                continue;
            };
            let library = entry.file_name().to_string_lossy().contains(".so");
            if !metadata.is_file() || metadata.permissions().mode() & 0o111 == 0 || library {
                continue;
            }
            programs = true;
            let foreign =
                host.and_then(|host| elf_machine(&path).filter(|&machine| machine != host));
            if let Some(machine) = foreign {
                return Ok(Inspection::Foreign(machine));
            }
        }
    }
    Ok(if programs {
        Inspection::Fit
    }
    else {
        Inspection::Empty
    })
}

/// The machine of the ELF program at `path`, or none for another file.
///
/// # Specification
/// trivial.
#[inline]
fn elf_machine(path: &Path) -> Option<Machine>
{
    let mut header = [0_u8; 20];
    std::fs::File::open(path)
        .ok()?
        .read_exact(&mut header)
        .ok()?;
    let [
        m0,
        m1,
        m2,
        m3,
        _class,
        data,
        _,
        _,
        _,
        _,
        _,
        _,
        _,
        _,
        _,
        _,
        t0,
        t1,
        e0,
        e1,
    ] = header;
    if [m0, m1, m2, m3] != *b"\x7fELF" {
        return None;
    }
    let (kind, machine) = match data {
        1 => (u16::from_le_bytes([t0, t1]), u16::from_le_bytes([e0, e1])),
        // A big-endian header: its bytes, reversed, read as little-endian.
        2 => (u16::from_le_bytes([t1, t0]), u16::from_le_bytes([e1, e0])),
        _ => return None,
    };
    // An executable or a position-independent executable.
    matches!(kind, 2 | 3).then_some(Machine(machine))
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use super::Inspection;
    use super::Lack;
    use super::Listing;
    use super::Machine;
    use super::disabled;
    use super::inspect;
    use super::lacks;
    use crate::names::Json;
    use crate::names::ToolKey;
    use crate::names::Version;

    /// A scratch directory of the running test, empty: the test's thread
    /// names it.
    ///
    /// # Specification
    /// trivial.
    fn scratch() -> PathBuf
    {
        let test = std::thread::current()
            .name()
            .unwrap_or("test")
            .replace("::", "-");
        let directory =
            std::env::temp_dir().join(format!("host-tools-{}-{test}", std::process::id()));
        let _gone = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).unwrap();
        directory
    }

    /// A program at `path` whose ELF header names `machine`, little-endian.
    ///
    /// # Specification
    /// trivial.
    fn program(
        path: &Path,
        machine: Machine,
    )
    {
        use std::os::unix::fs::PermissionsExt as _;
        let mut header = vec![0x7f_u8, b'E', b'L', b'F', 2_u8, 1_u8];
        header.resize(16_usize, 0_u8);
        header.extend(3_u16.to_le_bytes());
        header.extend(machine.0.to_le_bytes());
        header.resize(64_usize, 0_u8);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, header).unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755_u32)).unwrap();
    }

    #[test]
    fn an_install_of_another_machine_and_an_empty_install_lack()
    {
        let root = scratch();
        let fit = root.join("fit");
        program(&fit.join("bin/tool"), Machine::RISCV);
        std::fs::write(fit.join("README"), "a file with no execute bit").unwrap();
        let foreign = root.join("foreign");
        program(&foreign.join("nested/bin/tool"), Machine::I386);
        let library = root.join("library");
        program(&library.join("bin/tool"), Machine::RISCV);
        program(&library.join("lib/libother.so.1"), Machine::X86_64);
        let empty = root.join("empty");
        std::fs::create_dir_all(empty.join("share")).unwrap();
        std::fs::write(empty.join("share/package.wasm"), "\0asm").unwrap();
        let host = Some(Machine::RISCV);
        assert_eq!(inspect(&fit, host), Ok(Inspection::Fit));
        assert_eq!(
            inspect(&foreign, host),
            Ok(Inspection::Foreign(Machine::I386))
        );
        assert_eq!(inspect(&library, host), Ok(Inspection::Fit));
        assert_eq!(inspect(&empty, host), Ok(Inspection::Empty));
        assert_eq!(inspect(&root.join("absent"), host), Ok(Inspection::Empty));
        assert_eq!(inspect(&foreign, None), Ok(Inspection::Fit));
        assert_eq!(
            Lack::Foreign {
                tool: "github:j178/prek".into(),
                version: "0.5.9".into(),
                machine: Machine::PPC64,
            }
            .to_string(),
            "holds github:j178/prek 0.5.9 for ppc64"
        );
        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_tool_whose_backend_needs_a_disabled_tool_stays_out()
    {
        let root = scratch();
        let fit = root.join("fit");
        program(&fit.join("bin/gh"), Machine::RISCV);
        let json = Json::from(
            format!(
                r#"{{
                    "github:cli/cli": [{{"version": "2.103.3", "installed": true, "install_path": "{}"}}],
                    "github:max-sixty/worktrunk": [{{"version": "0.81.0", "installed": false, "install_path": "{}"}}],
                    "npm:oxfmt": [{{"version": "0.75.0", "installed": false, "install_path": "{}"}}]
                }}"#,
                fit.display(),
                root.join("worktrunk").display(),
                root.join("oxfmt").display()
            )
            .as_str(),
        );
        let listing = Listing::read(&json).unwrap();
        let worktrunk = Lack::Absent {
            tool: "github:max-sixty/worktrunk".into(),
            version: Version::from("0.81.0"),
        };
        let host = Some(Machine::RISCV);
        assert_eq!(
            lacks(&listing, &[ToolKey::from("node")], host),
            Ok(vec![worktrunk.clone()])
        );
        assert_eq!(
            lacks(&listing, &[], host),
            Ok(vec![worktrunk, Lack::Absent {
                tool: "npm:oxfmt".into(),
                version: Version::from("0.75.0"),
            }])
        );
        assert!(Listing::read(&Json::from("[1, 2]")).is_err());
        assert_eq!(
            disabled(&Json::from("[\"node\"]\n")),
            Ok(vec![ToolKey::from("node")])
        );
        assert_eq!(disabled(&Json::from("[]\n")), Ok(Vec::new()));
        assert!(disabled(&Json::from("node")).is_err());
        std::fs::remove_dir_all(&root).unwrap();
    }
}
