#!/usr/bin/env bash
# The gate selection over a change too large for one argument (#5220), run by
# `check:gate-scope`. Each case builds a scratch repository whose change holds
# 4000 paths. Their list is longer than the 131072 bytes that Linux allows in
# one argument. No row of the table maps them, so the selection prints every
# check.
set -euo pipefail
here="$(cd "${BASH_SOURCE[0]%/*}" && pwd)"
source "$here/../cases/scratch.bash"
select="$here/select.bash"
source "$here/../pr-stack/trunk.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
tasks='["check:gate-scope","check:typos"]'
every=$'check:gate-scope\ncheck:typos'

fail() {
  echo "select case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A repository at `$1` whose `origin/$trunk`, the trunk of
# `.config/pr-stack/trunk.bash`, is its base commit, with 4000 untracked
# paths under `wide/`.
setup() {
  git init --quiet -b main "$1"
  cd "$1"
  identity
  : > base
  git add base && git commit --quiet -m base
  git update-ref "refs/remotes/origin/$trunk" HEAD
  mkdir wide
  for i in $(seq 1 4000); do : > "wide/a-path-that-no-row-of-the-table-maps-$i"; done
}

# The working change: 4000 untracked paths.
got=$(
  setup "$scratch/untracked"
  GATE_TASKS=$tasks "$select" 2>&1 || echo "exit $?"
)
[[ $got == "$every" ]] || fail "#5220: a working change of 4000 paths selects every check" "$got"

# The change of a commit: 4000 paths that one commit adds.
got=$(
  setup "$scratch/committed"
  git add wide && git commit --quiet -m wide
  GATE_TASKS=$tasks "$select" HEAD 2>&1 || echo "exit $?"
)
[[ $got == "$every" ]] || fail "#5220: a commit of 4000 paths selects every check" "$got"

(( failed == 0 )) || exit 1
echo "gate select OK: 2 changes past one argument's limit select every check"
