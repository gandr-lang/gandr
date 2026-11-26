#!/usr/bin/env bash
# The recovery sweep over the sources of a change (#5864), `ci:recovery-change`.
# The change is read against GANDR_SWEEP_BASE. Each corpus source it adds or
# modifies is named to `ci:recovery` in GANDR_RECOVERY_SOURCE, one name on
# each line, and the sweep visits those sources alone. A change to the parser,
# the grammar or the syntax tree can move the parse of every source, so it
# runs the whole sweep. A deleted source has nothing to sweep. A change with
# no such path sweeps nothing. A source's name is its root's prefix and its
# path below the root, as `Roots::asked` in `crates/workflow-sweep` states:
# `crates/surface-corpus/strict` is `strict`, and `corpus` is `fixture` with
# `ledger` and `sketch` held out.
set -euo pipefail
base=${GANDR_SWEEP_BASE:?ci:recovery-change: set GANDR_SWEEP_BASE to the revision the change is measured against}
if ! git rev-parse --verify --quiet "$base^{commit}" > /dev/null; then
  echo "ci:recovery-change: the base $base cannot be read; fetch it, or set GANDR_SWEEP_BASE" >&2
  exit 2
fi
whole=
names=()
while IFS=$'\t' read -r status path; do
  case $path in
    crates/surface-parser/* | crates/surface-grammar/* | crates/surface-syntax/*)
      whole="$path reaches every source"
      ;;
    corpus/ledger/* | corpus/sketch/*) ;;
    corpus/*.gandr | crates/surface-corpus/strict/*.gandr)
      if [[ $status == D ]]; then
        :
      elif [[ $path == corpus/* ]]; then
        names+=("fixture/${path#corpus/}")
      else
        names+=("strict/${path#crates/surface-corpus/strict/}")
      fi
      ;;
  esac
done < <(git diff --no-renames --name-status "$base" HEAD)
if [[ -n $whole ]]; then
  echo "ci:recovery-change: $whole; the whole sweep runs"
  exec mise run ci:recovery
fi
if ((${#names[@]} == 0)); then
  echo "ci:recovery-change: the change adds or modifies no corpus source; nothing to sweep"
  exit 0
fi
sources=$(printf '%s\n' "${names[@]}" | sort -u)
echo "ci:recovery-change: sweeping $(wc -l <<< "$sources" | tr -d ' ') source(s):"
sed 's/^/  /' <<< "$sources"
GANDR_RECOVERY_SOURCE=$sources exec mise run ci:recovery
