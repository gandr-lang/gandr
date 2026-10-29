#!/usr/bin/env bash
# The debugger a `debug:` task runs: `lldb` or `lldb-dap`, run on the
# arguments under a memory bound.
#
# Xcode's lldb names each variant of a Rust enum by the low 32 bits of its
# discriminant value, so over a wider tag the formatters cannot tell the
# variant (#3778). On macOS this is LLVM's lldb from Homebrew's `lldb`
# formula, which builds it with Python and runs Xcode's `debugserver`. Absent,
# it refuses with the install line. Elsewhere it is the one on PATH.
#
# A debugger that reads a wrong length can allocate without end, and a session
# that takes the host's memory takes every process beside it (#3823). So the
# debugger runs bounded to 8 GiB. Where a user systemd manager runs, the bound
# is a scope of its own with that `MemoryMax` and no swap: it holds lldb, its
# server and the program debugged together, and the kernel kills inside it
# alone. Elsewhere the bound is `ulimit -v`, or a tighter one already set.
# Where neither takes, it refuses.
#
# Usage: lldb.bash lldb|lldb-dap [args]... Exits 2 when the debugger is absent
# or no bound takes.
set -euo pipefail
tool=${1:?lldb.bash lldb|lldb-dap [args]...}
shift
bound_kib=$((8 * 1024 * 1024))
if [[ $(uname -s) == Darwin ]]; then
  prefix=$(brew --prefix lldb 2> /dev/null || true)
  if [[ -z $prefix || ! -x $prefix/bin/$tool ]]; then
    echo "debug: Xcode's $tool misnames Rust enum variants (#3778); install LLVM's: brew install lldb" >&2
    exit 2
  fi
  debugger=$prefix/bin/$tool
elif ! debugger=$(command -v "$tool"); then
  echo "debug: no $tool on PATH; install LLVM's lldb" >&2
  exit 2
fi
scope=(systemd-run --user --scope --quiet -p "MemoryMax=${bound_kib}K" -p MemorySwapMax=0 --)
if command -v systemd-run > /dev/null && "${scope[@]}" true 2> /dev/null; then
  exec "${scope[@]}" "$debugger" "$@"
fi
limit=$(ulimit -v)
if [[ $limit == unlimited ]] || ((limit > bound_kib)) && ! ulimit -v "$bound_kib" 2> /dev/null; then
  echo "debug: neither a systemd scope nor \`ulimit -v\` bounds $tool's memory here; it never runs unbounded (#3823)" >&2
  exit 2
fi
exec "$debugger" "$@"
