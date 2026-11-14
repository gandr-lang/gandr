//! The build script. With the `bindgen` feature off it does nothing, and the
//! build reads the checked-in declarations. With the feature on it makes the
//! kernel's `io_uring` declarations for the target's architecture.

/// Does nothing: the build reads the checked-in declarations.
///
/// # Specification
///
/// trivial.
#[cfg(not(feature = "bindgen"))]
fn main()
{
}

/// Makes the kernel's `io_uring` declarations for the target.
///
/// # Specification
///
/// - fails: the target's variable names a directory that holds no
///   `include/linux/io_uring.h`, or bindgen refuses the headers.
#[cfg(feature = "bindgen")]
fn main() -> ::std::io::Result<()>
{
    self::bindgen::bind()?;
    Ok(())
}

#[cfg(feature = "bindgen")]
/// The bindgen pass over the kernel's `io_uring` header.
mod bindgen
{
    /// The name of the variable that holds the kernel's headers for an
    /// architecture, or none for an architecture that the script does not
    /// name.
    ///
    /// # Specification
    ///
    /// trivial.
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            primitive_signature,
            reason = "the owner's script maps an architecture's name to a variable's name; #7645 owes a mend in place"
        )
    )]
    fn linux_headers(target_arch: &str) -> Option<&'static str>
    {
        match target_arch {
            "aarch64" => Some("arm64_LINUX_HEADERS"),
            "arm" | "armv7" => Some("arm_LINUX_HEADERS"),
            "loongarch64" => Some("loongarch_LINUX_HEADERS"),
            "powerpc" | "powerpc64" | "powerpc64le" => Some("powerpc_LINUX_HEADERS"),
            "riscv64" => Some("riscv_LINUX_HEADERS"),
            "s390x" => Some("s390_LINUX_HEADERS"),
            "x86" => Some("i386_LINUX_HEADERS"),
            "x86_64" => Some("x86_64_LINUX_HEADERS"),
            _ => None,
        }
    }

    /// The wrapper header that bindgen reads: the kernel's `io_uring` header.
    #[expect(clippy::needless_raw_strings, reason = "readability")]
    const HEADER: &str = r#"
#include <linux/io_uring.h>
"#;

    /// Makes the declarations from the headers that the target's variable
    /// names, and writes them to `src/sys/sys_<arch>.rs`. With no variable
    /// for the target, or the variable not set, it makes nothing.
    ///
    /// # Specification
    ///
    /// - fails: the variable names a directory that holds no
    ///   `include/linux/io_uring.h`, bindgen refuses the headers, or the file
    ///   cannot be written.
    pub fn bind() -> ::std::io::Result<()>
    {
        use ::std::path::PathBuf;

        let target_arch =
            ::std::env::var("CARGO_CFG_TARGET_ARCH").map_err(::std::io::Error::other)?;
        let Some(variable) = self::linux_headers(&target_arch)
        else {
            return Ok(());
        };
        println!("cargo::rerun-if-env-changed={variable}");
        let Some(linux_headers) = ::std::env::var_os(variable)
        else {
            return Ok(());
        };
        let linux_headers = PathBuf::from(linux_headers);
        let header = linux_headers.join("include/linux/io_uring.h");
        if !header.is_file() {
            let msg = format!(
                "{variable} names {}, which holds no include/linux/io_uring.h",
                linux_headers.display()
            );
            return Err(::std::io::Error::other(msg));
        }

        let manifest_dir =
            ::std::env::var("CARGO_MANIFEST_DIR").map_err(::std::io::Error::other)?;
        let out_dir = PathBuf::from(manifest_dir).join("src/sys");
        let out_file = out_dir.join(format!("sys_{target_arch}.rs"));

        ::std::fs::create_dir_all(&out_dir)?;

        let builder = ::bindgen::Builder::default();
        builder
            .derive_default(true)
            .flexarray_dst(true)
            .generate_cstr(true)
            .use_core()
            .wrap_unsafe_ops(true)
            .header_contents("wrapper.h", HEADER)
            .clang_arg(format!("-I{}", linux_headers.join("include").display()))
            .allowlist_type("io_timespec.*")
            .allowlist_type("io_uring_.*")
            .allowlist_type("io_wq_.*")
            .generate()
            .map_err(::std::io::Error::other)?
            .write_to_file(out_file)?;

        Ok(())
    }
}
