#!/usr/bin/env bash
# The debugger a `debug:` task runs: prints the path of `lldb` or `lldb-dap`.
#
# Xcode's lldb names each variant of a Rust enum by the low 32 bits of its
# discriminant value, so over a wider tag the formatters cannot tell the
# variant (#3778). On macOS this is LLVM's lldb from Homebrew's `lldb`
# formula, which builds it with Python and runs Xcode's `debugserver`. Absent,
# it refuses with the install line. Elsewhere it is the one on PATH.
#
# Usage: lldb.bash lldb|lldb-dap. Exits 2 when the debugger is absent.
set -euo pipefail
tool=${1:?lldb.bash lldb|lldb-dap}
if [[ $(uname -s) == Darwin ]]; then
  prefix=$(brew --prefix lldb 2> /dev/null || true)
  if [[ -z $prefix || ! -x $prefix/bin/$tool ]]; then
    echo "debug: Xcode's $tool misnames Rust enum variants (#3778); install LLVM's: brew install lldb" >&2
    exit 2
  fi
  printf '%s\n' "$prefix/bin/$tool"
elif ! command -v "$tool"; then
  echo "debug: no $tool on PATH; install LLVM's lldb" >&2
  exit 2
fi
