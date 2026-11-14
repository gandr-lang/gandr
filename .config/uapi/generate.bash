#!/usr/bin/env bash
# Writes the one UAPI file of `gandr-storage-io` from the pinned kernel: the
# io_uring layouts, which every 64-bit Linux architecture shares, and the
# table of the system calls that the crate issues, by architecture. The
# first run fetches the pinned tarball, checks its digest, installs its
# headers into the cache and keeps the system-call tables; each later run
# reads the cache. bindgen and libclang serve this generation alone, and the
# crate's build needs neither.
#
# Usage: generate.bash [output file]
set -euo pipefail

version=7.3.3
sha256=79c66dde66cd96877fcde8f7d36aec946b1f423d2b97b5a7b1751b75c764f3d1
cache="${XDG_CACHE_HOME:-$HOME/.cache}/gandr/linux-$version"
out="${1:-crates/storage-io/src/uapi.rs}"

if [[ ! -f $cache/ready ]]; then
  rm -rf "$cache"
  mkdir -p "$cache/tables"
  tarball="$cache/linux-$version.tar.xz"
  curl -sSfL -o "$tarball" "https://cdn.kernel.org/pub/linux/kernel/v${version%%.*}.x/linux-$version.tar.xz"
  printf '%s  %s\n' "$sha256" "$tarball" | sha256sum --check --quiet -
  tar -xJf "$tarball" -C "$cache"
  source="$cache/linux-$version"
  make -s -C "$source" ARCH=x86 INSTALL_HDR_PATH="$cache/headers" headers_install
  cp "$source/arch/x86/entry/syscalls/syscall_64.tbl" "$cache/tables/x86_64.tbl"
  cp "$source/scripts/syscall.tbl" "$cache/tables/generic.tbl"
  cp "$source/arch/powerpc/kernel/syscalls/syscall.tbl" "$cache/tables/powerpc64.tbl"
  cp "$source/arch/s390/kernel/syscalls/syscall.tbl" "$cache/tables/s390x.tbl"
  rm -rf "$tarball" "$source"
  touch "$cache/ready"
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
printf '#include <linux/io_uring.h>\n' > "$work/wrapper.h"

# The system calls that the crate issues. Each architecture's table names
# each call once, in the ABI that a 64-bit process uses.
calls=(io_uring_setup io_uring_enter io_uring_register mmap munmap)
table() {
  local file=$1 abis=$2 call number
  for call in "${calls[@]}"; do
    number=$(awk -v call="$call" -v abis="$abis" '
      $0 !~ /^[[:space:]]*#/ && NF >= 3 && $3 == call && index(" " abis " ", " " $2 " ") { print $1; exit }
    ' "$cache/tables/$file")
    if [[ -z $number ]]; then
      echo "generate.bash: $file names no $call in the ABIs $abis" >&2
      exit 1
    fi
    printf '    pub const %s: u32 = %s;\n' "${call^^}" "$number"
  done
}

{
  printf '%s\n' \
    '//! The io_uring UAPI of the pinned kernel, as `mise run uapi:generate` writes it;' \
    '//! `check:uapi` regenerates it and refuses a difference. The layouts are' \
    '//! the same on each 64-bit Linux architecture. The table gives each system' \
    '//! call that the crate issues its number on each architecture.' \
    "//! Kernel: linux-$version." \
    '' \
    '#![allow(' \
    '    dead_code,' \
    '    non_camel_case_types,' \
    '    non_upper_case_globals,' \
    '    clippy::all,' \
    '    clippy::pedantic,' \
    '    clippy::restriction,' \
    '    clippy::nursery,' \
    '    reason = "bindgen writes this file from the kernel headers"' \
    ')]' \
    ''
  # The union of the SQE's last 16 bytes holds a zero-size member, so
  # bindgen would wrap it in a helper type with functions: it stays opaque,
  # 16 bytes the crate never reads. The CQE's flexible tail would take the
  # helper `__IncompleteArrayField`: the filter below drops the helper and
  # writes the tail as a zero-length array, the same layout. So the file
  # declares no function, and each layout is the kernel's.
  bindgen "$work/wrapper.h" \
    --use-core \
    --no-layout-tests \
    --no-doc-comments \
    --no-prepend-enum-name \
    --default-enum-style consts \
    --formatter none \
    --allowlist-type 'io_uring_params|io_sqring_offsets|io_cqring_offsets|io_uring_sqe|io_uring_cqe|io_uring_op' \
    --allowlist-var 'IORING_.*|IOSQE_.*' \
    --opaque-type 'io_uring_sqe__bindgen_ty_6' \
    -- -I"$cache/headers/include" > "$work/bindings.rs"
  rustfmt --edition 2024 --config-path "$(git rev-parse --show-toplevel)/rustfmt.toml" "$work/bindings.rs"
  awk '
    /^#\[/ { held = held $0 "\n"; next }
    /^pub struct __IncompleteArrayField/ { held = ""; next }
    /^impl<T> .*__IncompleteArrayField<T>/ { skipping = 1; held = ""; next }
    skipping { if ($0 ~ /^}/) skipping = 0; next }
    {
      line = $0
      while (match(line, /__IncompleteArrayField<[A-Za-z0-9_]+>/)) {
        inner = substr(line, RSTART + 23, RLENGTH - 24)
        line = substr(line, 1, RSTART - 1) "[" inner "; 0]" substr(line, RSTART + RLENGTH)
      }
      printf "%s%s\n", held, line
      held = ""
    }
    END { printf "%s", held }
  ' "$work/bindings.rs" > "$work/layouts.rs"
  if grep -q -e '__IncompleteArrayField' -e '__BindgenUnionField' -e '\bfn ' "$work/layouts.rs"; then
    echo 'generate.bash: the layouts still declare a function or a helper' >&2
    exit 1
  fi
  cat "$work/layouts.rs"
  printf '\n%s\n' '/// The number of each system call that the crate issues, on each architecture.'
  printf '%s\n' 'pub mod syscall {'
  for arch in x86_64:x86_64.tbl:'common 64' riscv64:generic.tbl:'common 64 riscv' aarch64:generic.tbl:'common 64' loongarch64:generic.tbl:'common 64' powerpc64:powerpc64.tbl:'common 64 nospu' s390x:s390x.tbl:'common 64'; do
    IFS=: read -r name file abis <<< "$arch"
    printf '    #[cfg(target_arch = "%s")]\n' "$name"
    printf '    mod %s {\n' "$name"
    table "$file" "$abis" | sed 's/^/    /'
    printf '    }\n'
    printf '    #[cfg(target_arch = "%s")]\n' "$name"
    printf '    pub use self::%s::*;\n' "$name"
  done
  printf '%s\n' '}'
} > "$work/uapi.rs"

# The tree's rustfmt formats the file as the commit's treefmt does, so a
# regeneration and the committed file compare byte for byte.
rustfmt --edition 2024 --config-path "$(git rev-parse --show-toplevel)/rustfmt.toml" "$work/uapi.rs"

mkdir -p "$(dirname "$out")"
mv "$work/uapi.rs" "$out"
