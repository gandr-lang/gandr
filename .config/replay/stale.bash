#!/usr/bin/env bash
# What a replay leaves stale (#6144). A replay moves a branch's own commits
# onto a base that moved, with no conflict, and keeps each generated artifact
# the commits hold. An artifact written on the old base can then disagree
# with inputs the new base changed, and nothing the merge queue requires
# reads it: #6127's replay onto #6125's last head left 5 recovery records
# stale on the landing.
#
# Each row of `artifacts.json` names one generated artifact: the paths it
# lives at, the paths it derives from, the check that regenerates and
# compares it, and the command that records it again. `due.jq` reads the rows
# the replay makes due. The script runs each due row's check on the head, in
# the current directory, which must hold the head's tree. A check reads the
# new base as `REPLAY_BASE`, and mise trusts the directory, as `pr:land` runs
# the reading in a scratch worktree.
#
# `pr:open` runs it on the head it stacks, and `chain_replay` on each member
# that a restack, a cut or a signed restack replays, before anything moves.
# On a runner the replay reads `--due` alone (#6159).
#
# Usage:
#   stale.bash <old base> <new base> <head>
#     Runs the due checks. Exits 0 when none is due or each passes. Exits 1,
#     naming each stale artifact and the command that records it again.
#   stale.bash --due <old base> <new base> <head>
#     Prints the due rows as a JSON array, and runs nothing.
#
# `REPLAY_ARTIFACTS`, when set, names the table to read in place of
# `artifacts.json`, as the restack cases give their own.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
due_only=false
if [[ ${1:-} == --due ]]; then
  due_only=true
  shift
fi
(( $# == 3 )) || { echo 'usage: stale.bash [--due] <old base> <new base> <head>' >&2; exit 2; }
old=$(git rev-parse "$1^{commit}")
new=$(git rev-parse "$2^{commit}")
head=$(git rev-parse "$3^{commit}")
# The path lists reach jq as files, never as arguments: a large replay makes a
# list longer than one argument can hold (#5220).
due=$(jq -n -c \
  --slurpfile rows "${REPLAY_ARTIFACTS:-$here/artifacts.json}" \
  --rawfile moved <(git diff --no-renames --name-only "$old" "$new") \
  --rawfile own <(git diff --no-renames --name-only "$new" "$head") \
  --rawfile crates <(git ls-tree -d --name-only "$head" crates/) \
  'def lines: split("\n") | map(select(. != ""));
   {rows: $rows[0], moved: ($moved | lines), own: ($own | lines), crates: ($crates | lines | map(ltrimstr("crates/")))}' \
  | jq -c -f "$here/due.jq")
if $due_only; then
  echo "$due"
  exit 0
fi
[[ $due != '[]' ]] || exit 0
if [[ $(git rev-parse 'HEAD^{tree}') != "$(git rev-parse "$head^{tree}")" ]]; then
  echo "replay: the checks of ${head::12} run on its tree, and this worktree holds another" >&2
  exit 2
fi
trusted=$(git rev-parse --show-toplevel)${MISE_TRUSTED_CONFIG_PATHS:+:$MISE_TRUSTED_CONFIG_PATHS}
status=0
while IFS=$'\t' read -r name check record; do
  echo "replay: the base moved what $name read under ${head::12}; \`$check\` reads them again" >&2
  if ! REPLAY_BASE=$new MISE_TRUSTED_CONFIG_PATHS=$trusted bash -c "$check" >&2; then
    echo "replay: $name are stale on ${head::12}; record them again with \`$record\` on the branch, and land again" >&2
    status=1
  fi
done < <(jq -r '.[] | [.name, .check, .record] | @tsv' <<< "$due")
exit "$status"
