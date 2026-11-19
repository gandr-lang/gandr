#!/usr/bin/env bash
# The five counts of recovery in a pull request's body. `pr:open` reads them:
#
#   counts.bash <base> <body>
#
# A change can touch the parser, its grammar or its syntax tree. Its body then
# states the counts of `ledger:recovery` at its base and at its head. They
# stand in a `### Recovery` subsection:
#
#   - base: <the last line of ledger:recovery at the base>
#   - head: <the last line of ledger:recovery at the head>
#
# The script computes both lines, the base in a scratch worktree. It refuses
# a body that states other lines, and it names the lines to write.
#
# The script also measures the share "marked where they were made" at the
# base and at the head. A fall of more than one point is refused. The owner's
# word admits a fall in one line: `- fall: admitted by the owner, <where>`.
#
# A change that touches none of the three crates passes with no subsection.
# `RECOVERY_LEDGER` names the command that prints the counts in a tree, for
# the cases.
#
# - see: #8152
set -euo pipefail
base=${1:?usage: counts.bash <base> <body>}
body=${2:?usage: counts.bash <base> <body>}
root=$(git rev-parse --show-toplevel)
read -ra ledger <<< "${RECOVERY_LEDGER:-mise run --quiet ledger:recovery}"
touched=$(git -C "$root" diff --name-only "$base" HEAD -- crates/surface-parser/ crates/surface-grammar/ crates/surface-syntax/)
[[ -n $touched ]] || exit 0
counted() {
  (cd "$1" && CARGO_TARGET_DIR="$root/target/recovery-counts" "${ledger[@]}") \
    | awk '/ mutants swept: /{line = $0} END {print line}'
}
scratch=$(mktemp -d)
trap 'git -C "$root" worktree remove --force "$scratch/base" > /dev/null 2>&1 || :; rm -rf "$scratch"' EXIT
git -C "$root" worktree add --quiet --detach "$scratch/base" "$base"
head_line=$(counted "$root")
base_line=$(counted "$scratch/base")
if [[ -z $head_line || -z $base_line ]]; then
  echo "recovery: ledger:recovery printed no counts at the base or at the head" >&2
  exit 1
fi
section=$(awk '/^### Recovery[[:space:]]*$/ {on = 1; next} on && /^#/ {exit} on' "$body")
stated_base=$(sed -n 's/^- base: //p' <<< "$section")
stated_head=$(sed -n 's/^- head: //p' <<< "$section")
if [[ $stated_base != "$base_line" || $stated_head != "$head_line" ]]; then
  printf 'recovery: the body states other counts than ledger:recovery computes; write this subsection:\n\n### Recovery\n\n- base: %s\n- head: %s\n' "$base_line" "$head_line" >&2
  exit 2
fi
fall=$(printf '%s\n%s\n' "$base_line" "$head_line" \
  | awk '{share[NR] = 100 * $4 / $1} END {printf "%.2f", share[1] - share[2]}')
if awk -v fall="$fall" 'BEGIN {exit !(fall > 1)}' && ! grep -q '^- fall: admitted by the owner' <<< "$section"; then
  printf 'recovery: the share marked where they were made falls %s points from the base to the head, more than one; repair it, or state `- fall: admitted by the owner, <where>`\n' "$fall" >&2
  exit 2
fi
echo "recovery: the body states the counts at the base and at the head, and the share falls ${fall} points"
