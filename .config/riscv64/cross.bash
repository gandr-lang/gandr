#!/usr/bin/env bash
# Runs a command under the settings that build for riscv64 on an x86-64 host
# of ours. The host's path holds the cross linker and its riscv64 C library.
# `check:riscv64-ring` runs under these settings.
# - see: #7720
#
# Usage: cross.bash <command> [<argument>...]
set -euo pipefail
export CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_LINKER=riscv64-linux-gnu-gcc
exec "$@"
