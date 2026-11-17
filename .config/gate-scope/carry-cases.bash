#!/usr/bin/env bash
# The gate carry over a restack (#5153, `passed.bash carry`), run by
# `check:gate-scope`. Each case builds a scratch repository: a base commit on
# `main`, a branch `own` with one commit gated on its tree, and a top `top`
# that a restack rebases `own` onto. The case reads whether the gate carries
# to the rebased tree.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
passed=$here/passed.bash
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "carry case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A repository at `$1` with `main`, `own` (one commit on `shared`) and `top`
# (one commit on the file `$2`), and a gate record for the tree of `own`.
setup() {
  git init --quiet -b main "$1"
  cd "$1"
  identity
  printf 'one\ntwo\nthree\n' > shared
  git add shared && git commit --quiet -m base
  git checkout --quiet -b top
  printf 'top\n' >> "$2"
  git add "$2" && git commit --quiet -m top
  git checkout --quiet -b own main
  printf 'one\nown\nthree\n' > shared
  git add shared && git commit --quiet -m own
  records=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-gate/$(git rev-parse 'HEAD^{tree}')
  mkdir -p "$records"
  jq -n --arg tree "$(git rev-parse 'HEAD^{tree}')" --arg commit "$(git rev-parse HEAD)" \
    '{tree: $tree, commit: $commit, gate: "check", checks: ["check:gate-scope"], tasks: ["check:gate-scope"]}' > "$records/a.json"
}

# Whether a record names the tree of HEAD, carried from another tree.
carried() {
  local dir
  dir=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-gate/$(git rev-parse 'HEAD^{tree}')
  compgen -G "$dir/*.json" > /dev/null && jq -e '.carried != null' "$dir"/*.json > /dev/null
}

# A top that touches another file keeps the branch's patch: the gate carries.
got=$(
  setup "$scratch/apart" other
  gated=$(git rev-parse HEAD)
  git rebase --quiet top
  if "$passed" carry "$gated" HEAD top > /dev/null; then
    if carried; then echo carried; else echo "carried, with no record"; fi
  else echo refused; fi
)
[[ $got == carried ]] || fail "#5153: a restack onto a top that touches other files carries the gate" "$got"

# A top that touches the branch's lines changes its patch: the gate does not
# carry, and no record names the new tree.
got=$(
  setup "$scratch/overlap" shared
  gated=$(git rev-parse HEAD)
  git rebase --quiet top 2> /dev/null || {
    printf 'one\nown\nthree\ntop\nresolved\n' > shared
    git add shared
    GIT_EDITOR=true git rebase --continue > /dev/null
  }
  if "$passed" carry "$gated" HEAD top > /dev/null 2>&1; then echo carried
  elif carried; then echo "refused, with a record"
  else echo refused; fi
)
[[ $got == refused ]] || fail "#5153: a restack that changes the branch's patch carries no gate" "$got"

# A head on the gated tree needs no carry and writes no record.
got=$(
  setup "$scratch/same" other
  if "$passed" carry HEAD HEAD main > /dev/null; then
    if carried; then echo "kept, with a carried record"; else echo kept; fi
  else echo refused; fi
)
[[ $got == kept ]] || fail "#5153: a head on the gated tree keeps its own record" "$got"

(( failed == 0 )) || exit 1
echo "gate carry OK: 3 cases carry, refuse and keep as recorded"
