#!/usr/bin/env bash
# The probe of #7284, which never lands: the holds of a walk that keeps.
# Each module of `library/std/src` is readmitted after an edit that puts a
# definition first, at one thread and at the pool's width, and then the
# generated module of 2,000 forms runs its script of edits. Each readmission
# prints one `PROBE` line with its counts on standard error.
set -euo pipefail
cargo build --release --locked -p gandr-surface-session --example edit_loop
ex=target/release/examples/edit_loop
echo "host: $(uname -m), $(nproc) threads"
for f in $(find library/std/src -name '*.gandr' | sort); do
  REPEATS=1 PROBE_BASE="$f" "$ex" 2>&1 > /dev/null | awk -v f="$f" '/^PROBE base threads=/ { print f, $0 }'
done
REPEATS=1 "$ex" 2>&1 > /dev/null | awk '/^PROBE root=/'
