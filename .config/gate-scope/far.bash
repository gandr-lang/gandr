#!/usr/bin/env bash
# The far side of `gate:remote` (#6996). `remote.bash` sends this file over
# ssh to another host of ours and runs it there with `bash -s`. The far host
# can run the bash of macOS, version 3.2, so the file uses no array that can
# be empty and no `mapfile`.
#
# Usage:
#   far.bash probe <checkout> [reader]
#     Prints `{"load": <l>, "cores": <n>, "free": <k>, "token": <t>}`: the
#     host's load over one minute, its cores, the gate slots that no gate
#     holds, and whether a gate there reads with a token: `GH_TOKEN`, or the
#     token of <reader> from the host's gh. The slots and the host lock are
#     those of the checkout's own tree (`.config/mise/gate.bash`). The probe
#     takes each free slot for an instant and lets it go.
#   far.bash gate <checkout> <origin> <trunk> <branch> <commit> <lane> [reader]
#     Runs the landing's gate, `mise run check`, on <commit> in the lane's
#     clone, `gandr/gate-remote/<lane>` under the state directory. The
#     host's tools come first (`mise run tools:check`, #7127). A missing tool
#     stops the gate before its build. It exits with status 2.
#
#     The gate's lines go to standard error as they arrive. On a pass, its
#     pass records go to standard output. The far gate publishes its verdict
#     records to the remote. Then `remote.bash` admits the pass. A failed or
#     stopped gate prints no record and returns its status.
#
# A seat's gate runs with `GH_TOKEN` set, and an ssh session has none.
# `remote.bash` writes the reader's token from its own host's gh before this
# file on the remote shell's standard input, so the gate holds it before
# its first read of GitHub. With no token handed, the host's wrapper of gh
# asks the next gh on `PATH` for a token, and in a case over a gh stub that
# is the stub, which refuses (#6644, as the head watcher's `watch_token`).
# The account that the wrapper gives with no name can be the owner's. So the
# far gate then takes the token of <reader>, the account that reads, from
# the host's gh. A token already set stays.
#
# A relative <checkout> is read from the home directory. The clone links the
# objects of the checkout, as the head watcher's clone does
# (`.config/integration/watch.bash`), so it copies no object. Its name is the
# lane, so its gate takes that lane's lock (`gate_lane`). It keeps its target
# directory from one head to the next, so a lane's later gate builds what
# changed since its last one. The branch keeps its name in the clone, so the
# gate reads the claim of the branch's unit (`.config/claims/taken.bash`).
set -euo pipefail

usage() {
  echo 'usage: far.bash (probe <checkout> [reader] | gate <checkout> <origin> <trunk> <branch> <commit> <lane> [reader])' >&2
  exit 2
}

# Ends the far gate's process group when its local SSH session closes.
session_closed() {
  local group=$1
  while IFS= read -r; do :; done
  kill -TERM -- "-$group"
}

# Stops the session reader and releases the far caller's lane lock.
far_exit() {
  local status=$?
  kill "$far_session_watcher" 2> /dev/null || :
  wait "$far_session_watcher" 2> /dev/null || :
  host_unlock 8 || :
  return "$status"
}

case ${1:-} in
  probe)
    (( $# == 2 || $# == 3 )) || usage
    reader=${3:-}
    cd "$HOME" && cd "$2"
    source .config/mise/gate.bash
    if [[ -r /proc/loadavg ]]; then
      read -r load _ < /proc/loadavg
    else
      load=$(sysctl -n vm.loadavg | awk '{ print $2 }')
    fi
    dir=$(host_lock_dir)
    dir=${dir%/}/gandr
    mkdir -p "$dir"
    free=0
    for (( n = 1; n <= gate_slots; n++ )); do
      exec 7<> "$dir/gate.$n.lock"
      if host_flock 7; then free=$(( free + 1 )); fi
      exec 7<&-
    done
    token=true
    if [[ -z ${GH_TOKEN:-} && -n $reader ]] && ! gh auth token --user "$reader" > /dev/null 2>&1; then token=false; fi
    # A checkout older than the head may name no `gate_cores`, so the probe
    # reads the cores itself.
    printf '{"load": %s, "cores": %s, "free": %s, "token": %s}\n' "$load" "$(getconf _NPROCESSORS_ONLN)" "$free" "$token"
    ;;
  gate)
    (( $# == 7 || $# == 8 )) || usage
    origin=$3
    trunk=$4
    branch=$5
    commit=$6
    lane=$7
    reader=${8:-}
    session_token=
    IFS= read -r session_token || exit 1
    if [[ -n $session_token ]]; then export GH_TOKEN=$session_token; fi
    cd "$HOME" && cd "$2"
    source .config/mise/gate.bash
    session_group=$(host_group "$$")
    [[ -n $session_group ]] || exit 2
    exec 6<&0
    session_closed "$session_group" <&6 &
    far_session_watcher=$!
    exec 6<&-
    trap 'exit 143' TERM HUP
    host_lock --fd 8 "gate-lane-$lane" 1 "gate:remote of $commit"
    export GANDR_GATE_LANE_LOCKED=$lane
    trap far_exit EXIT
    clone=${XDG_STATE_HOME:-$HOME/.local/state}/gandr-factory/gate-remote/$lane
    if [[ ! -d $clone/.git ]]; then
      mkdir -p "${clone%/*}"
      git clone --quiet --no-checkout "$(git rev-parse --path-format=absolute --git-common-dir)" "$clone"
    fi
    cd "$clone"
    git remote set-url origin "$origin"
    # A clone of a shallow repository is shallow too; the first fetch makes
    # it whole, as the head watcher's does.
    if [[ $(git rev-parse --is-shallow-repository) == true ]]; then
      git fetch --quiet --unshallow origin "+refs/heads/$trunk:refs/remotes/origin/$trunk" "+refs/heads/$branch:refs/remotes/origin/$branch"
    else
      git fetch --quiet origin "+refs/heads/$trunk:refs/remotes/origin/$trunk" "+refs/heads/$branch:refs/remotes/origin/$branch"
    fi
    git checkout --quiet --force -B "$branch" "$commit"
    git clean --quiet --force -d
    mise trust --quiet "$clone" > /dev/null 2>&1 || :
    if [[ -z ${GH_TOKEN:-} && -n $reader ]] && token=$(gh auth token --user "$reader" 2> /dev/null) && [[ -n $token ]]; then
      export GH_TOKEN=$token
    fi
    echo "gate:remote: the gate of $commit runs on $(hostname -s) in the clone of the lane $lane" >&2
    mise run tools:check >&2
    mise run check >&2
    .config/gate-scope/verdict.bash publish HEAD \
      || echo "gate:remote: the verdict records were not sent, so hosted jobs run their checks again (#8166)" >&2
    records=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-gate/$(git rev-parse 'HEAD^{tree}')
    for file in "$records"/*.json; do
      if [[ -e $file ]]; then cat "$file"; fi
    done
    ;;
  *)
    usage
    ;;
esac
