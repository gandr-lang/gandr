#!/usr/bin/env bash
# The debugger a `debug:` task runs: `lldb` or `lldb-dap`, run on the
# arguments, under a memory bound off macOS.
#
# Xcode's lldb names each variant of a Rust enum by the low 32 bits of its
# discriminant value, so over a wider tag the formatters cannot tell the
# variant (#3778). On macOS this is LLVM's lldb from Homebrew's `lldb`
# formula, which builds it with Python and runs Xcode's `debugserver`. Absent,
# it refuses with the install line. Elsewhere it is the one on PATH.
#
# A debugger that reads a wrong length can allocate without end, and a session
# that takes the host's memory takes every process beside it (#3823). The
# formatters bound every read to the process's mapped memory everywhere. Off
# macOS the debugger also runs under `.config/mise/bounded`, the 8 GiB bound a
# scope with no swap sets where a user systemd manager runs: it holds lldb, its
# server and the program debugged together. Elsewhere the bound is `ulimit -v`,
# and where neither takes, it refuses. macOS has no systemd, and its kernel
# refuses to lower `ulimit -v`, so there the formatters' read bound is the only
# one (#3863).
#
# Usage: lldb.bash lldb|lldb-dap [args]... Exits 2 when the debugger is absent
# or, off macOS, no bound takes.
set -euo pipefail
tool=${1:?lldb.bash lldb|lldb-dap [args]...}
shift
if [[ $(uname -s) == Darwin ]]; then
  prefix=$(brew --prefix lldb 2> /dev/null || true)
  if [[ -z $prefix || ! -x $prefix/bin/$tool ]]; then
    echo "debug: Xcode's $tool misnames Rust enum variants (#3778); install LLVM's: brew install lldb" >&2
    exit 2
  fi
  exec "$prefix/bin/$tool" "$@"
fi
if ! debugger=$(command -v "$tool"); then
  echo "debug: no $tool on PATH; install LLVM's lldb" >&2
  exit 2
fi
exec "${BASH_SOURCE[0]%/*}/../mise/bounded" debug "$debugger" "$@"
