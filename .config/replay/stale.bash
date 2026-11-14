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
# compares it, and the command that records it again. A row MAY name
# `stale`, the exit statuses of its check that mean the artifacts disagree
# (#6786): for a nextest check, 100, a red test. Another failing status is
# the check's own error, as a package that no crate holds (101). A row with
# no `stale` reads each failing status as stale. `due.jq` reads the rows
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
#     Exits 2 when a check fails on its own, naming the check and its status:
#     the replay then cannot read the artifacts.
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
# Each check runs in the environment of the head's tree, never in the caller's
# (#7485). mise sets `RUSTUP_TOOLCHAIN` and the paths of the tools from the
# tree where it starts, and the variable overrides `rust-toolchain.toml`. So
# the seat's environment can carry the pin of another tree. `mise exec` in the
# head's tree gives each check the tools, the variables and the pin of that
# tree. The script also gives the pin directly, for a tree whose mise
# configuration does not read it. A tree that pins no toolchain is refused by
# name. The replay installs nothing: a tool that the tree pins and the host
# lacks fails its check.
toolchain=$({ git show "$head:rust-toolchain.toml" 2> /dev/null || :; } | sed -n 's/^channel = "\([^"]*\)".*/\1/p')
if [[ -z $toolchain ]]; then
  echo "replay: the tree of ${head::12} pins no toolchain in rust-toolchain.toml, so its checks do not run under the caller's" >&2
  exit 2
fi
status=0
while IFS=$'\t' read -r name check record stale; do
  echo "replay: the base moved what $name read under ${head::12}; \`$check\` reads them again" >&2
  ran=0
  REPLAY_BASE=$new MISE_TRUSTED_CONFIG_PATHS=$trusted MISE_EXEC_AUTO_INSTALL=false RUSTUP_TOOLCHAIN=$toolchain \
    mise exec -- bash -c "$check" >&2 || ran=$?
  (( ran != 0 )) || continue
  if [[ -z $stale || " $stale " == *" $ran "* ]]; then
    echo "replay: $name are stale on ${head::12}; record them again with \`$record\` on the branch, and land again" >&2
    (( status == 2 )) || status=1
  else
    echo "replay: \`$check\` fails on its own with status $ran, not with a stale artifact ($stale), so it reads nothing of $name; repair the check" >&2
    status=2
  fi
done < <(jq -r '.[] | [.name, .check, .record, ((.stale // []) | map(tostring) | join(" "))] | @tsv' <<< "$due")
exit "$status"
