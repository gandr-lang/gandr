#!/usr/bin/env bash
# The far side of the Linux part of `check:doc-targets`. It fetches one
# commit from the temporary ref that names it, documents that exact checkout,
# and returns its tree.
set -euo pipefail

usage() {
  echo 'usage: targets-far.bash doc-targets <checkout> <origin> <ref> <commit> <lane>' >&2
  exit 2
}

# Ends the native documentation pass when the local SSH session closes.
session_closed() {
  local group=$1
  while IFS= read -r; do :; done
  kill -TERM -- "-$group"
}

# Stops the session reader and releases the lane lock.
far_exit() {
  local status=$?
  kill "$far_session_watcher" 2> /dev/null || :
  wait "$far_session_watcher" 2> /dev/null || :
  host_unlock 8 || :
  return "$status"
}

case ${1:-} in
  doc-targets)
    (( $# == 6 )) || usage
    [[ $(uname -s) == Linux ]] || { echo 'doc-targets: the configured Linux host does not run Linux' >&2; exit 2; }
    origin=$3
    ref=$4
    commit=$5
    lane=$6
    IFS= read -r _ || exit 1
    cd "$HOME" && cd "$2"
    source .config/mise/gate.bash
    session_group=$(host_group "$$")
    [[ -n $session_group ]] || exit 2
    exec 6<&0
    session_closed "$session_group" <&6 &
    far_session_watcher=$!
    exec 6<&-
    trap 'exit 143' TERM HUP
    host_lock --fd 8 "doc-targets-$lane" 1 "doc-targets of $commit"
    export GANDR_GATE_LANE_LOCKED=$lane
    trap far_exit EXIT
    clone=${XDG_STATE_HOME:-$HOME/.local/state}/gandr-factory/doc-targets/$lane
    if [[ ! -d $clone/.git ]]; then
      mkdir -p "${clone%/*}"
      git clone --quiet --no-checkout "$(git rev-parse --path-format=absolute --git-common-dir)" "$clone"
    fi
    cd "$clone"
    git remote set-url origin "$origin"
    git fetch --quiet origin "$ref:refs/remotes/doc-targets/$commit"
    [[ $(git rev-parse "refs/remotes/doc-targets/$commit") == "$commit" ]] \
      || { echo 'doc-targets: the Linux pass received another commit' >&2; exit 2; }
    git checkout --quiet --force --detach "$commit"
    git clean --quiet --force -d
    mise trust --quiet "$clone" > /dev/null 2>&1 || :
    mise run tools:check >&2
    GANDR_DOC_TARGETS_NATIVE=1 bash .config/doc/targets-cases.bash >&2
    printf '{"tree":"%s","commit":"%s"}\n' "$(git rev-parse 'HEAD^{tree}')" "$commit"
    ;;
  *) usage ;;
esac
