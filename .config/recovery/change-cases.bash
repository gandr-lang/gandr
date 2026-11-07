#!/usr/bin/env bash
# The records `ci:recovery-change` sweeps for each shape of a change (#5864).
# Each case commits a change over a scratch repository's base and runs
# `change.bash` against that base. A stub `mise` stands for `ci:recovery` and
# prints the sources GANDR_RECOVERY_SOURCE names, or `every source` when the
# variable is unset. The result is that line, or the line the task prints
# when it sweeps nothing.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-recovery-change.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

source "$here/../cases/scratch.bash"

fail() {
  printf 'recovery-change case %s\n  got: %s\n' "$1" "$2" >&2
  failed=1
}

mkdir "$work/bin"
cat > "$work/bin/mise" << 'STUB'
#!/usr/bin/env bash
[[ $* == "run ci:recovery" ]] || { echo "stub mise: $*" >&2; exit 1; }
if [[ -v GANDR_RECOVERY_SOURCE ]]; then
  echo "swept: $(paste -sd ' ' - <<< "$GANDR_RECOVERY_SOURCE")"
else
  echo "swept: every source"
fi
STUB
chmod +x "$work/bin/mise"

# A scratch repository at `$1` whose base holds a fixture source with its
# record, a strict source with its record, a held-out ledger source, a parser
# source and a README.
setup() {
  git init --quiet --initial-branch=main "$1"
  cd "$1"
  identity
  mkdir -p corpus/model/data corpus/ledger crates/surface-corpus/strict crates/surface-parser/src \
    crates/surface-parser/tests/recovery/fixture/model/data crates/surface-parser/tests/recovery/strict
  echo 'maybe' > corpus/model/data/data-maybe.gandr
  echo 'ledger' > corpus/ledger/rows.gandr
  echo 'values' > crates/surface-corpus/strict/values.gandr
  echo 'parser' > crates/surface-parser/src/lib.rs
  echo 'rows' > crates/surface-parser/tests/recovery/fixture/model/data/data-maybe.recovery
  echo 'rows' > crates/surface-parser/tests/recovery/strict/values.recovery
  echo 'readme' > README.md
  git add -A
  git commit --quiet -m base
  base=$(git rev-parse HEAD)
}

# Commit the working tree and run the task against the base; print the line
# the sweep or the task gives.
sweep() {
  git add -A
  git commit --quiet -m change
  PATH="$work/bin:$PATH" GANDR_SWEEP_BASE=$base "$here/change.bash" | awk '/^swept: |nothing to sweep/'
}

got=$(
  setup "$work/one"
  echo 'maybe, edited' > corpus/model/data/data-maybe.gandr
  sweep
)
[[ $got == "swept: fixture/model/data/data-maybe.gandr" ]] || fail "#5864: a change to one corpus source sweeps that source's record alone" "$got"

got=$(
  setup "$work/new"
  echo 'new' > corpus/model/data/data-new.gandr
  echo 'rows, edited' > crates/surface-parser/tests/recovery/strict/values.recovery
  sweep
)
[[ $got == "swept: fixture/model/data/data-new.gandr strict/values.gandr" ]] || fail "#5864: a new source and an edited record each name their source" "$got"

got=$(
  setup "$work/strict"
  echo 'values, edited' > crates/surface-corpus/strict/values.gandr
  sweep
)
[[ $got == "swept: strict/values.gandr" ]] || fail "#5864: a strict source is named under its root's prefix" "$got"

got=$(
  setup "$work/parser"
  echo 'parser, edited' > crates/surface-parser/src/lib.rs
  echo 'maybe, edited' > corpus/model/data/data-maybe.gandr
  sweep
)
[[ $got == "swept: every source" ]] || fail "#5864: a change to the parser runs the whole sweep" "$got"

got=$(
  setup "$work/renamed"
  git mv corpus/model/data/data-maybe.gandr corpus/model/data/maybe.gandr
  sweep
)
[[ $got == "swept: every source" ]] || fail "#5864: a renamed source runs the whole sweep, for the record it leaves" "$got"

got=$(
  setup "$work/none"
  echo 'readme, edited' > README.md
  echo 'ledger, edited' > corpus/ledger/rows.gandr
  sweep
)
[[ $got == *"nothing to sweep" ]] || fail "#5864: a change with no corpus source, a held-out one aside, sweeps nothing" "$got"

(( failed == 0 )) || exit 1
echo "recovery-change OK: 6 cases sweep a change's own records, the whole sweep for the parser or a removed source, and nothing for no source"
