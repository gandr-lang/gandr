#!/usr/bin/env bash
# The script delegates the Linux part of `check:doc-targets` from a
# non-Linux gate. XDG configuration names the host.
#
# The far script documents the exact committed tree from a temporary ref. The
# common git directory records one verdict under the tree hash.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(cd "$here/../.." && pwd)
config=${GANDR_GATE_HOSTS:-${XDG_CONFIG_HOME:-$HOME/.config}/gandr-factory/gate-hosts.json}

fail() {
  printf 'doc-targets: %s\n' "$*" >&2
  exit 2
}

[[ -r $config ]] || fail 'no Linux host is configured'
host=$(jq -r '.doc_targets.linux // empty' "$config")
[[ -n $host ]] || fail 'no Linux host is configured'
jq -e --arg host "$host" '
  .hosts[$host]
  | (.ssh | (type == "array" and length > 0))
  and (.checkout | (type == "string" and length > 0))
' "$config" > /dev/null || fail 'the configured Linux host has no connection'

git symbolic-ref --quiet --short HEAD > /dev/null || fail 'the Linux pass requires a branch'
commit=$(git rev-parse HEAD)
tree=$(git rev-parse 'HEAD^{tree}')
[[ $("$root/.config/gate-scope/passed.bash" tree) == "$tree" ]] \
  || fail 'the Linux pass requires its own commit'
records=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-doc-targets
cache=$records/$tree.json
if [[ -r $cache ]] && jq -e --arg tree "$tree" '.tree == $tree' "$cache" > /dev/null; then
  echo 'doc-targets check OK: the Linux pass is kept for this tree'
  exit 0
fi

ssh_of() {
  jq -r --arg host "$1" '.hosts[$host].ssh[]' "$config"
}

# Runs the remote verifier with a pipe that ends when this process ends. The
# far side uses that end to stop its process group and release its lane lock.
far() {
  local selected=$1 ssh=() word script command session status=0 ssh_pid
  shift
  while IFS= read -r word; do ssh+=("$word"); done < <(ssh_of "$selected")
  script=$(< "$here/targets-far.bash")
  printf -v command 'exec bash -c %q --' "$script"
  for word in "$@"; do printf -v command '%s %q' "$command" "$word"; done
  session=$(mktemp -d)
  mkfifo "$session/session"
  "${ssh[@]}" "bash -c $(printf '%q' "$command")" < "$session/session" &
  ssh_pid=$!
  exec 7> "$session/session"
  printf '\n' >&7
  wait "$ssh_pid" || status=$?
  exec 7>&-
  rm -rf "$session"
  return "$status"
}

ref=refs/doc-targets/$commit
if ! existing=$(git ls-remote --refs origin "$ref"); then
  fail 'the Linux pass cannot read its commit ref'
fi
if [[ -z $existing ]]; then
  git push --quiet origin "$commit:$ref" || fail 'the Linux pass cannot create its commit ref'
elif [[ $existing != "$commit"$'\t'"$ref" ]]; then
  fail 'the Linux pass found its commit ref at another commit'
fi
if ! existing=$(git ls-remote --refs origin "$ref"); then
  fail 'the Linux pass cannot read its commit ref'
fi
[[ $existing == "$commit"$'\t'"$ref" ]] || fail 'the Linux pass did not create its exact commit ref'
mkdir -p "$records"
record=$(mktemp "$records/.record.XXXXXX")
trap 'rm -f "$record"' EXIT
if ! far "$host" doc-targets "$(jq -r --arg host "$host" '.hosts[$host].checkout' "$config")" \
  "$(git remote get-url origin)" "$ref" "$commit" "${GANDR_GATE_LANE:-local}" > "$record"; then
  fail 'the configured Linux host did not answer or refused its pass'
fi
jq -e --arg tree "$tree" --arg commit "$commit" '.tree == $tree and .commit == $commit' "$record" > /dev/null \
  || fail 'the Linux pass returned no verdict for this tree'
if ! existing=$(git ls-remote --refs origin "$ref"); then
  fail 'the Linux pass cannot read its commit ref'
fi
[[ $existing == "$commit"$'\t'"$ref" ]] || fail 'the Linux pass found its commit ref at another commit'
git push --quiet origin ":$ref" || fail 'the Linux pass cannot remove its commit ref'
mv "$record" "$cache"
echo 'doc-targets check OK: the Linux pass completed for this tree'
