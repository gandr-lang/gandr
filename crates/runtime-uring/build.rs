#![expect(
    clippy::missing_docs_in_private_items,
    clippy::wildcard_imports,
    reason = "build"
)]
#![expect(
    dead_code,
    reason = "the owner's `Config::target_arch` and `cargo::feature` stay unread, and without `bindgen` so do the fields its pass reads"
)]

use ::std::path::Path;
use ::std::path::PathBuf;

fn main() -> ::std::io::Result<()>
{
    self::run()?;
    Ok(())
}

fn run() -> ::std::io::Result<()>
{
    println!("cargo::rustc-check-cfg=cfg(asm_experimental_arch)");
    if !crate::target::os::is_linux()? {
        return Ok(());
    }

    let config = crate::config::Config::new()?;
    crate::target::check()?;

    if let Some(linux_headers_dir) = &config.linux_headers_dir {
        crate::cargo::rerun(linux_headers_dir);
        #[cfg(feature = "bindgen")]
        crate::bindgen::bind(&config, linux_headers_dir)?;
    }

    Ok(())
}

#[cfg(feature = "bindgen")]
mod bindgen
{
    use super::*;

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
            .raw_line(r#"#![expect(clippy::as_conversions, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::as_pointer_underscore, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::decimal_literal_representation, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::empty_structs_with_brackets, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::indexing_slicing, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::missing_const_for_fn, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::multiple_unsafe_ops_per_block, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::ptr_as_ptr, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::ref_as_ptr, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::renamed_function_params, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::transmute_ptr_to_ptr, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::undocumented_unsafe_blocks, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::unreadable_literal, reason = "bindgen")]"#)
            .raw_line(r#"#![expect(clippy::use_self, reason = "bindgen")]"#)

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

mod cargo
{
    pub mod cfg
    {
        pub fn has(cfg: &str) -> bool
        {
            let cfg = cfg.to_uppercase();
            let cfg = format!("CARGO_CFG_{cfg}");
            crate::cargo::var(&cfg).is_ok()
        }

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

    pub mod feature
    {
        pub fn has(feature: &str) -> bool
        {
            let feature = feature.to_uppercase();
            let feature = format!("CARGO_FEATURE_{feature}");
            crate::cargo::var(&feature).is_ok()
        }
    }

    pub fn rerun(linux_headers_dir: &str)
    {
        println!("cargo::rerun-if-env-changed=CARGO_CFG_TARGET_ARCH");
        println!("cargo::rerun-if-env-changed=CARGO_MANIFEST_DIR");
        println!("cargo::rerun-if-changed={linux_headers_dir}/include/linux/io_uring.h");
    }

    pub fn var(var: &str) -> ::std::io::Result<String>
    {
        ::std::env::var(var).map_err(|_err| {
            let msg = format!(r#"Environment variable not found: "{var}""#);
            ::std::io::Error::other(msg)
        })
    }
}

mod config
{
    use super::*;

    #[derive(Debug)]
    pub struct Config
    {
        pub target_arch: String,
        pub target_arch_dir: PathBuf,
        pub target_arch_mod: PathBuf,
        pub linux_headers_env: String,
        pub linux_headers_dir: Option<String>,
        pub req_feature_experimental_asm: bool,
    }

    impl Config
    {
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

mod linux
{
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

    pub mod headers
    {
        pub fn env(linux_arch: &str) -> String
        {
            format!("{linux_arch}_LINUX_HEADERS")
        }

        pub fn path(linux_headers_env: &str) -> Option<String>
        {
            println!("cargo::rerun-if-env-changed={linux_headers_env}");
            ::std::env::var(linux_headers_env).ok()
        }
    }
}

#[expect(clippy::unnecessary_wraps, reason = "WIP")]
mod target
{
    use super::*;

    pub fn check() -> ::std::io::Result<()>
    {
        crate::target::arch::check()?;
        crate::target::os::check()?;
        crate::target::abi::check()?;
        Ok(())
    }

    pub mod abi
    {
        pub const fn check() -> ::std::io::Result<()>
        {
            Ok(())
        }
    }

    pub mod arch
    {
        use super::*;

        pub const fn check() -> ::std::io::Result<()>
        {
            Ok(())
        }

        pub fn dir(manifest_dir: &str) -> PathBuf
        {
            PathBuf::from(manifest_dir).join("src/base/sys/linux/uapi/arch")
        }

        pub fn r#mod(
            arch_dir: &Path,
            target_arch: &str,
        ) -> PathBuf
        {
            arch_dir.join(format!("{target_arch}.rs"))
        }
    }

    pub mod os
    {
        pub fn is_linux() -> ::std::io::Result<bool>
        {
            Ok(crate::cargo::var("CARGO_CFG_TARGET_OS")? == "linux")
        }

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
