#![expect(clippy::missing_docs_in_private_items, reason = "build")]

#[cfg(not(feature = "bindgen"))]
fn main()
{
}

#[cfg(feature = "bindgen")]
fn main() -> ::std::io::Result<()>
{
    self::bindgen::bind()?;
    Ok(())
}

#[cfg(feature = "bindgen")]
mod bindgen
{
    fn linux_headers(target_arch: &str) -> ::std::io::Result<&'static str>
    {
        match target_arch {
            "aarch64" => Ok("arm64_LINUX_HEADERS"),
            "arm" | "armv7" => Ok("arm_LINUX_HEADERS"),
            "loongarch64" => Ok("loongarch_LINUX_HEADERS"),
            "powerpc" | "powerpc64" | "powerpc64le" => Ok("powerpc_LINUX_HEADERS"),
            "riscv64gc" => Ok("riscv_LINUX_HEADERS"),
            "s390x" => Ok("s390_LINUX_HEADERS"),
            "x86" => Ok("i386_LINUX_HEADERS"),
            "x86_64" => Ok("x86_64_LINUX_HEADERS"),
            _ => {
                let msg = format!("Unsupported target arch: \"{target_arch}\"");
                let err = ::std::io::Error::other(msg);
                Err(err)
            },
        }
    }

    #[expect(clippy::needless_raw_strings, reason = "readability")]
    const HEADER: &str = r#"
#include <linux/io_uring.h>
"#;

    pub fn bind() -> ::std::io::Result<()>
    {
        use ::std::path::PathBuf;

        let target_arch =
            ::std::env::var("CARGO_CFG_TARGET_ARCH").map_err(::std::io::Error::other)?;
        let linux_headers = self::linux_headers(&target_arch)?;
        let linux_headers = ::std::env::var(linux_headers).map_err(::std::io::Error::other)?;

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
            .clang_arg(format!("-I{linux_headers}/include"))
            .allowlist_type("io_timespec.*")
            .allowlist_type("io_uring_.*")
            .allowlist_type("io_wq_.*")
            .generate()
            .map_err(::std::io::Error::other)?
            .write_to_file(out_file)?;

        Ok(())
    }
}
