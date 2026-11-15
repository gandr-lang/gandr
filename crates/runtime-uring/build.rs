//! The owner's build script. It names the cfg of the powerpc asm feature, and
//! on Linux it checks the target. With the `bindgen` feature on and the
//! target's headers variable set, it makes the kernel's declarations for the
//! target's architecture under `src/base/sys/linux/uapi/arch`.

// The script's helpers take the names that Cargo and the kernel give as
// strings. #7717 gives each a newtype, as it does for the crate's preparers.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the helpers take the names that Cargo and the kernel give as strings; #7717 owes each mend"
    )
)]

/// Runs the script.
///
/// # Specification
///
/// - fails: as [`run`] fails.
/// - executable: none — the script's effect is the build's, observable only by
///   building.
///
/// # Adequacy
///
/// - hypothesis: L2 — the base's declarations that the script makes set up a
///   ring on the host. A wrong layout or a wrong number fails the setup.
/// - witness: `base::io_uring::test::setup`
fn main() -> ::std::io::Result<()>
{
    self::run()?;
    Ok(())
}

/// Names the cfg of the powerpc asm feature. On Linux it checks the target,
/// and with the headers variable set it makes the declarations.
///
/// # Specification
///
/// - fails: Cargo names no target, the target is not one that the script knows,
///   powerpc builds without the asm cfg, the variable names a directory that
///   holds no `include/linux/io_uring.h`, or bindgen refuses the headers.
/// - executable: none — the script's effect is the build's, observable only by
///   building.
///
/// # Adequacy
///
/// - hypothesis: L2 — as [`main`].
/// - witness: `base::io_uring::test::setup`
fn run() -> ::std::io::Result<()>
{
    println!("cargo::rustc-check-cfg=cfg(asm_experimental_arch)");
    if !crate::target::os::is_linux()? {
        return Ok(());
    }

    let config = crate::config::Config::new()?;
    crate::target::check()?;

    if let Some(linux_headers_dir) = config.linux_headers_dir.as_deref() {
        crate::cargo::rerun(linux_headers_dir);
        #[cfg(feature = "bindgen")]
        crate::bindgen::bind(&config, linux_headers_dir)?;
    }

    Ok(())
}

/// The bindgen pass over the kernel's headers.
#[cfg(feature = "bindgen")]
mod bindgen
{
    use ::std::path::Path;

    /// The wrapper header that bindgen reads: each kernel header whose
    /// declarations the base names.
    #[expect(clippy::needless_raw_strings, reason = "readability")]
    const HEADER: &str = r#"
#include <asm/unistd.h>
#include <asm/fcntl.h>
#include <linux/mman.h>
#include <linux/fcntl.h>
#include <linux/io_uring.h>
#include <linux/time_types.h>
#include <linux/uio.h>
#include <linux/openat2.h>
#include <linux/stat.h>
#include <linux/eventpoll.h>
#include <linux/futex.h>
#include <linux/wait.h>
#include <linux/socket.h>
#include <linux/un.h>
#include <asm/siginfo.h>
"#;

    /// Makes the declarations from the headers under `linux_headers_dir`, and
    /// writes them to the target's file.
    ///
    /// # Specification
    ///
    /// - fails: the directory holds no `include/linux/io_uring.h`, bindgen
    ///   refuses the headers, or the file cannot be written.
    /// - executable: none — the made file is code that the crate compiles.
    ///
    /// # Cost
    ///
    /// - allocation: the paths, the message and the made declarations, setup
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L2 — as [`main`](crate::main).
    /// - witness: `base::io_uring::test::setup`
    pub fn bind(
        config: &crate::config::Config,
        linux_headers_dir: &str,
    ) -> ::std::io::Result<()>
    {
        let header = Path::new(linux_headers_dir).join("include/linux/io_uring.h");
        if !header.is_file() {
            let msg = format!(
                "{} names {linux_headers_dir}, which holds no include/linux/io_uring.h",
                config.linux_headers_env
            );
            return Err(::std::io::Error::other(msg));
        }
        ::std::fs::create_dir_all(&config.target_arch_dir)?;
        let bindings = self::builder(linux_headers_dir)
            .generate()
            .map_err(::std::io::Error::other)?;
        bindings.write_to_file(&config.target_arch_mod)?;
        Ok(())
    }

    /// The bindgen builder over the headers under `linux_headers`, with the
    /// expectations that the made file carries.
    ///
    /// # Specification
    ///
    /// trivial.
    ///
    /// # Cost
    ///
    /// - allocation: the builder and its options, setup
    fn builder(linux_headers: &str) -> ::bindgen::Builder
    {
        ::bindgen::Builder::default()
            // rustc lints
            .raw_line(r#"#![expect(dead_code, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(non_camel_case_types, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(non_upper_case_globals, reason = "bindgen")]"#)

            // clippy lints
            .raw_line(r#"#![cfg_attr(not(test), expect(clippy::missing_docs_in_private_items, reason = "bindgen"))]"#)
            .raw_line(r#"#![expect(clippy::allow_attributes, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::allow_attributes_without_reason, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::arithmetic_side_effects, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::as_conversions, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::as_pointer_underscore, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::decimal_literal_representation, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::doc_markdown, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::empty_structs_with_brackets, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::indexing_slicing, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::inline_trait_bounds, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::missing_const_for_fn, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::multiple_unsafe_ops_per_block, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::ptr_as_ptr, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::ref_as_ptr, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::renamed_function_params, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::tabs_in_doc_comments, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::transmute_ptr_to_ptr, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::undocumented_unsafe_blocks, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::unreadable_literal, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::use_self, reason = "bindgen")]"#)

            // quenchant lints
            .raw_line(r#"#![cfg_attr(dylint_lib = "quenchant_dylints", expect(raw_pointer_through_reference, reason = "bindgen"))]"#)
            .raw_line(r#"#![cfg_attr(dylint_lib = "quenchant_dylints", expect(specification_present, reason = "bindgen"))]"#)
            // The safety lint runs before `cfg_attr` expands, so only a plain
            // attribute reaches it. rustc alone does not know its name.
            .raw_line(r#"#![allow(unknown_lints, reason = "bindgen: rustc alone does not know the quenchant lint below")]"#)
            .raw_line(r#"#![allow(unsafe_safety_documentation, reason = "bindgen: the made helpers carry no safety section")]"#)

            // compiler configuration
            .header_contents("wrapper.h", HEADER)
            .clang_arg(format!("-I{linux_headers}/include"))

            // code-gen configuration
            .use_core()
            .generate_cstr(true)
            .derive_default(true)
            // NOTE: This almost works but some of the unions confuse bindgen.
            // .flexarray_dst(true)
            .size_t_is_usize(false)
            .wrap_unsafe_ops(true)

            //
            .allowlist_type("io_timespec.*")
            .allowlist_type("io_uring_.*")
            .allowlist_type("io_wq_.*")
            .allowlist_type("__kernel_timespec")
            .allowlist_type("__kernel_mode_t")
            .allowlist_type("__kernel_off_t")
            .allowlist_type("__kernel_pid_t")
            .allowlist_type("__kernel_sockaddr_storage")
            .allowlist_type("iovec")
            .allowlist_type("open_how")
            .allowlist_type("statx")
            .allowlist_type("epoll_event")
            .allowlist_type("futex_waitv")
            .allowlist_type("sockaddr_un")
            .allowlist_type("siginfo_t")
            .allowlist_var("__NR_(io_uring_.*|mmap|munmap|madvise)")
            .allowlist_var("IORING_.*")
            .allowlist_var("IOSQE_.*")
            .allowlist_var("SPLICE_F_FD_IN_FIXED")
            .allowlist_var("PROT_(READ|WRITE)")
            .allowlist_var("MAP_(SHARED|POPULATE|ANONYMOUS|HUGETLB|HUGE_SHIFT|HUGE_2MB)")
            .allowlist_var("MADV_DONTFORK")
            .allowlist_var("O_(NONBLOCK|CLOEXEC)")
            .allowlist_var("AT_FDCWD")
            .allowlist_var("P_(ALL|PID|PGID|PIDFD)")
    }
}

/// What the script reads from Cargo and says to it.
mod cargo
{
    /// The cfgs that Cargo sets for the target.
    pub mod cfg
    {
        /// Whether Cargo sets the cfg `cfg`.
        ///
        /// # Specification
        ///
        /// trivial.
        ///
        /// # Cost
        ///
        /// - allocation: the variable's name, setup
        pub fn has(cfg: &str) -> bool
        {
            let cfg = cfg.to_uppercase();
            let cfg = format!("CARGO_CFG_{cfg}");
            crate::cargo::var(&cfg).is_ok()
        }

        /// Turns the cfg `feature` on for the crate, which the build must set.
        ///
        /// # Specification
        ///
        /// - fails: Cargo does not set the cfg.
        /// - executable: none — a reading of Cargo's variables.
        ///
        /// # Cost
        ///
        /// - allocation: the refusal's message, error path
        ///
        /// # Adequacy
        ///
        /// - hypothesis: L2 — as [`main`](crate::main).
        /// - witness: `base::io_uring::test::setup`
        pub fn r#use(feature: &str) -> ::std::io::Result<()>
        {
            if !crate::cargo::cfg::has(feature) {
                let msg = format!("Required feature must be enabled with --cfg={feature}");
                return Err(::std::io::Error::other(msg));
            }
            println!("cargo:rustc-cfg={feature}");
            Ok(())
        }
    }

    /// The features that Cargo turns on for the crate.
    pub mod feature
    {
        /// Whether Cargo turns the feature `feature` on.
        ///
        /// # Specification
        ///
        /// trivial.
        ///
        /// # Cost
        ///
        /// - allocation: the variable's name, setup
        #[expect(
            dead_code,
            reason = "the owner's script names it, and no step reads it yet"
        )]
        pub fn has(feature: &str) -> bool
        {
            let feature = feature.to_uppercase();
            let feature = format!("CARGO_FEATURE_{feature}");
            crate::cargo::var(&feature).is_ok()
        }
    }

    /// Asks Cargo to run the script again when the target, the manifest's
    /// directory or the ring's header changes.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn rerun(linux_headers_dir: &str)
    {
        println!("cargo::rerun-if-env-changed=CARGO_CFG_TARGET_ARCH");
        println!("cargo::rerun-if-env-changed=CARGO_MANIFEST_DIR");
        println!("cargo::rerun-if-changed={linux_headers_dir}/include/linux/io_uring.h");
    }

    /// The value of the variable `var` that Cargo sets.
    ///
    /// # Specification
    ///
    /// - fails: Cargo does not set the variable, and the error names it.
    /// - executable: none — a reading of Cargo's variables.
    ///
    /// # Cost
    ///
    /// - allocation: the variable's value and the refusal's message, setup
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L2 — as [`main`](crate::main).
    /// - witness: `base::io_uring::test::setup`
    pub fn var(var: &str) -> ::std::io::Result<String>
    {
        ::std::env::var(var).map_err(|_err| {
            let msg = format!(r#"Environment variable not found: "{var}""#);
            ::std::io::Error::other(msg)
        })
    }
}

/// The script's view of the target and of the headers.
mod config
{
    use ::std::path::PathBuf;

    /// The target's architecture, its file of declarations, and the
    /// variable and directory of its headers.
    #[derive(Debug)]
    pub struct Config
    {
        /// The target's architecture, as Cargo names it.
        #[expect(
            dead_code,
            reason = "the owner's script keeps it, and no step reads it yet"
        )]
        pub target_arch: String,
        /// The directory of the declarations' files.
        #[cfg_attr(
            not(feature = "bindgen"),
            expect(dead_code, reason = "the bindgen pass alone reads it")
        )]
        pub target_arch_dir: PathBuf,
        /// The file of the target's declarations.
        #[cfg_attr(
            not(feature = "bindgen"),
            expect(dead_code, reason = "the bindgen pass alone reads it")
        )]
        pub target_arch_mod: PathBuf,
        /// The name of the variable of the target's headers.
        #[cfg_attr(
            not(feature = "bindgen"),
            expect(dead_code, reason = "the bindgen pass alone reads it")
        )]
        pub linux_headers_env: String,
        /// The directory of the target's headers, when the variable is set.
        pub linux_headers_dir: Option<String>,
        /// Whether the target needs the asm feature: powerpc does.
        pub req_feature_experimental_asm: bool,
    }

    impl Config
    {
        /// The view of the target that Cargo builds for.
        ///
        /// # Specification
        ///
        /// - fails: Cargo names no target or no manifest directory, the target
        ///   is not one that the script knows, or powerpc builds without the
        ///   asm cfg.
        /// - executable: none — a reading of Cargo's variables.
        ///
        /// # Cost
        ///
        /// - allocation: the target's names and paths, setup
        ///
        /// # Adequacy
        ///
        /// - hypothesis: L2 — as [`main`](crate::main).
        /// - witness: `base::io_uring::test::setup`
        pub fn new() -> ::std::io::Result<Self>
        {
            let target_arch =
                ::std::env::var("CARGO_CFG_TARGET_ARCH").map_err(::std::io::Error::other)?;
            let linux_arch = crate::linux::arch(&target_arch)?;
            let linux_headers_env = crate::linux::headers::env(linux_arch);
            let linux_headers_dir = crate::linux::headers::path(&linux_headers_env);

            let manifest_dir =
                ::std::env::var("CARGO_MANIFEST_DIR").map_err(::std::io::Error::other)?;
            let target_arch_dir = crate::target::arch::dir(&manifest_dir);
            let target_arch_mod = crate::target::arch::r#mod(&target_arch_dir, &target_arch);

            let req_feature_experimental_asm = ["powerpc", "powerpc64"].contains(&&*target_arch);

            let this = Self {
                target_arch,
                target_arch_dir,
                target_arch_mod,
                linux_headers_env,
                linux_headers_dir,
                req_feature_experimental_asm,
            };

            this.check()?;

            Ok(this)
        }

        /// Checks the target's system, and turns the asm cfg on where the
        /// target needs it.
        ///
        /// # Specification
        ///
        /// - fails: the target's system is not Linux, or powerpc builds without
        ///   the asm cfg.
        /// - executable: none — a reading of Cargo's variables.
        ///
        /// # Adequacy
        ///
        /// - hypothesis: L2 — as [`main`](crate::main).
        /// - witness: `base::io_uring::test::setup`
        fn check(&self) -> ::std::io::Result<()>
        {
            crate::target::os::check()?;

            if self.req_feature_experimental_asm {
                crate::cargo::cfg::r#use("asm_experimental_arch")?;
            }

            Ok(())
        }
    }
}

/// The kernel's names of the architectures and of their headers.
mod linux
{
    /// The kernel's name of the architecture that Cargo names `target_arch`.
    ///
    /// # Specification
    ///
    /// - fails: the script does not know the architecture.
    /// - executable: none — a table of names.
    ///
    /// # Cost
    ///
    /// - allocation: the refusal's message, error path
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L2 — as [`main`](crate::main).
    /// - witness: `base::io_uring::test::setup`
    pub fn arch(target_arch: &str) -> ::std::io::Result<&'static str>
    {
        match target_arch {
            "aarch64" => Ok("arm64"),
            "arm" | "armv7" => Ok("arm"),
            "loongarch64" => Ok("loongarch"),
            "powerpc" | "powerpc64" | "powerpc64le" => Ok("powerpc"),
            "riscv64" => Ok("riscv"),
            "s390x" => Ok("s390"),
            "x86" => Ok("i386"),
            "x86_64" => Ok("x86_64"),
            _ => {
                let msg = format!("Unsupported target arch: \"{target_arch}\"");
                Err(::std::io::Error::other(msg))
            },
        }
    }

    /// The variable of each architecture's headers.
    pub mod headers
    {
        /// The name of the variable of the headers of `linux_arch`.
        ///
        /// # Specification
        ///
        /// trivial.
        ///
        /// # Cost
        ///
        /// - allocation: the variable's name, setup
        pub fn env(linux_arch: &str) -> String
        {
            format!("{linux_arch}_LINUX_HEADERS")
        }

        /// The directory that the variable `linux_headers_env` names, when it
        /// is set. Cargo runs the script again when the variable changes.
        ///
        /// # Specification
        ///
        /// trivial.
        ///
        /// # Cost
        ///
        /// - allocation: the directory's name, setup
        pub fn path(linux_headers_env: &str) -> Option<String>
        {
            println!("cargo::rerun-if-env-changed={linux_headers_env}");
            ::std::env::var(linux_headers_env).ok()
        }
    }
}

/// The checks of the target, and the place of its declarations.
mod target
{
    /// Checks the target's architecture, system and ABI.
    ///
    /// # Specification
    ///
    /// - fails: the target's system is not Linux.
    /// - executable: none — a reading of Cargo's variables.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L2 — as [`main`](crate::main).
    /// - witness: `base::io_uring::test::setup`
    pub fn check() -> ::std::io::Result<()>
    {
        crate::target::arch::check()?;
        crate::target::os::check()?;
        crate::target::abi::check()?;
        Ok(())
    }

    /// The target's ABI.
    pub mod abi
    {
        /// Checks the target's ABI: each ABI passes for now.
        ///
        /// # Specification
        ///
        /// trivial.
        #[expect(
            clippy::unnecessary_wraps,
            reason = "the owner's check keeps the form of a check that can fail"
        )]
        pub const fn check() -> ::std::io::Result<()>
        {
            Ok(())
        }
    }

    /// The target's architecture.
    pub mod arch
    {
        use ::std::path::Path;
        use ::std::path::PathBuf;

        /// Checks the target's architecture: each architecture passes for now.
        ///
        /// # Specification
        ///
        /// trivial.
        #[expect(
            clippy::unnecessary_wraps,
            reason = "the owner's check keeps the form of a check that can fail"
        )]
        pub const fn check() -> ::std::io::Result<()>
        {
            Ok(())
        }

        /// The directory of the declarations' files under the manifest's
        /// directory `manifest_dir`.
        ///
        /// # Specification
        ///
        /// trivial.
        ///
        /// # Cost
        ///
        /// - allocation: the path, setup
        pub fn dir(manifest_dir: &str) -> PathBuf
        {
            PathBuf::from(manifest_dir).join("src/base/sys/linux/uapi/arch")
        }

        /// The file of the declarations of `target_arch` under `arch_dir`.
        ///
        /// # Specification
        ///
        /// trivial.
        ///
        /// # Cost
        ///
        /// - allocation: the path, setup
        pub fn r#mod(
            arch_dir: &Path,
            target_arch: &str,
        ) -> PathBuf
        {
            arch_dir.join(format!("{target_arch}.rs"))
        }
    }

    /// The target's system.
    pub mod os
    {
        /// Whether the target's system is Linux.
        ///
        /// # Specification
        ///
        /// - fails: Cargo names no target system.
        /// - executable: none — a reading of Cargo's variables.
        ///
        /// # Adequacy
        ///
        /// - hypothesis: L2 — as [`main`](crate::main).
        /// - witness: `base::io_uring::test::setup`
        pub fn is_linux() -> ::std::io::Result<bool>
        {
            Ok(crate::cargo::var("CARGO_CFG_TARGET_OS")? == "linux")
        }

        /// Checks that the target's system is Linux.
        ///
        /// # Specification
        ///
        /// - fails: Cargo names no target system, or the system is not Linux.
        /// - executable: none — a reading of Cargo's variables.
        ///
        /// # Cost
        ///
        /// - allocation: the refusal's message, error path
        ///
        /// # Adequacy
        ///
        /// - hypothesis: L2 — as [`main`](crate::main).
        /// - witness: `base::io_uring::test::setup`
        pub fn check() -> ::std::io::Result<()>
        {
            let var = "CARGO_CFG_TARGET_OS";
            match crate::cargo::var(var)?.as_str() {
                "linux" => Ok(()),
                target_os => {
                    let msg = format!(r#"Unsupported target OS: "{target_os}""#);
                    Err(::std::io::Error::other(msg))
                },
            }
        }
    }
}
