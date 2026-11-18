#!/usr/bin/env bash
# The cases of the licence check. `check:licences` runs them before the check
# reads the tree. Each case builds a scratch repository with a `deny.toml`
# that allows `MIT`. Its list approves one licence file, and the case adds
# its own files. This file writes each SPDX line from its parts, so the
# check of the tree reads none here.
# - see: #7743, `check.bash`
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "licence case FAILED: $1"
  echo "  got: $2"
  failed=1
}

spdx() { printf '// %s-%s: %s\n' SPDX License-Identifier "$1"; }
approved_text() { printf 'the approved licence text\n'; }

# A repository at `$1` whose list approves the digest of `approved_text`.
setup() {
  git init --quiet "$1"
  cd "$1"
  mkdir -p .config/licences
  printf '[licenses]\nallow = ["MIT", "Apache-2.0 WITH LLVM-exception"]\n' > deny.toml
  jq -n --arg digest "$(approved_text | sha256sum | cut -c1-64)" \
    '{files: {($digest): "the case'"'"'s licence"}}' > .config/licences/approved.json
  approved_text > LICENSE
}

# The verdict of the check over the repository: `pass`, or each refusal.
verdict() {
  git add -A
  if out=$("$here/check.bash" "$PWD" 2>&1); then echo pass; else echo "$out"; fi
}

got=$(setup "$scratch/base" && verdict)
[[ $got == pass ]] || fail "#7743: a tree of approved files passes" "$got"

got=$(setup "$scratch/copy" && mkdir -p crates/one && approved_text > crates/one/LICENSE-MIT && verdict)
[[ $got == pass ]] || fail "#7743: a new copy of an approved licence file passes where it stands" "$got"

got=$(setup "$scratch/beside" && mkdir -p crates/one && printf 'another licence\n' > crates/one/licence.txt && verdict)
[[ $got == *"the licence file crates/one/licence.txt"*"the owner alone approves"* ]] \
  || fail "#7743: a licence file beside a crate with a digest outside the list is refused, by its path" "$got"

got=$(setup "$scratch/directory" && mkdir -p LICENSES && printf 'another licence\n' > LICENSES/Other.txt && verdict)
[[ $got == *"the licence file LICENSES/Other.txt"* ]] || fail "#7743: a file in a LICENSES directory is a licence file" "$got"

got=$(setup "$scratch/spdx-in" && spdx 'MIT OR Apache-2.0 WITH LLVM-exception' > src.rs && verdict)
[[ $got == pass ]] || fail "#7743: an SPDX line of allowed licences passes" "$got"

got=$(setup "$scratch/spdx-out" && spdx '(MIT AND GPL-3.0-only)' > src.rs && verdict)
[[ $got == *"src.rs:1 brings GPL-3.0-only"*"the owner alone approves"* ]] \
  || fail "#7743: an SPDX line that brings a licence outside the allow list is refused, by the licence and its line" "$got"

got=$(setup "$scratch/no-list" && rm .config/licences/approved.json && verdict)
[[ $got == *"no .config/licences/approved.json"* ]] || fail "#7743: a tree with no list is refused" "$got"

(( failed == 0 )) || exit 1
echo "licence cases OK: 7 cases pass, refuse and name as recorded"
