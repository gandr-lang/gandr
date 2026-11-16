#!/usr/bin/env bash
# Runs a command under the settings that build for riscv64 on an x86-64 host
# of ours. The host's path holds the cross linker and its riscv64 C library.
# The night's archive and `check:riscv64-ring` run under these settings.
# - see: #7720, `.github/workflows/nightly-riscv64-tests.yml`
#
# On riscv64 the liburing crate of the ring makes its bindings with the
# bindgen command, which `mise.toml` pins. Release 0.72.1 of that command
# reads the riscv64 floating-point state of `ucontext_t` whole, 528 bytes.
# Its clang reads the riscv64 C library of the host by the sysroot.
#
# The configure step of liburing reads `CC`, so `CC` names the cross
# compiler. `HOST_CC` keeps the host's own C compiles on the host's compiler.
#
# Usage: cross.bash <command> [<argument>...]
set -euo pipefail
export CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_LINKER=riscv64-linux-gnu-gcc
BINDGEN_PATH=$(mise exec cargo:bindgen-cli -- which bindgen)
export BINDGEN_PATH
export BINDGEN_EXTRA_CLANG_ARGS_riscv64gc_unknown_linux_gnu=--sysroot=/usr/riscv64-linux-gnu
export CC=riscv64-linux-gnu-gcc HOST_CC=cc
exec "$@"
