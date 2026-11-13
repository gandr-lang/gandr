#!/usr/bin/env bash
# shellcheck disable=SC2154 # watch.bash and stall.bash, sourced below, set watch_home and stall_home
# The head watcher's service runs landing's own `watch.bash` (#6653), and the
# stall detector's service runs landing's own scripts (#7002), run by
# `check:integration`. The case sources the real scripts, with the state
# directory in a scratch directory, over a scratch remote whose `landing`
# holds a `watch.bash` that prints its version.
#
# - A lane's worktree makes the service's checkout. A sweep then removes the
#   lane's worktree, and the service's checkout stands.
# - `landing` takes a new `watch.bash`. The service sets its checkout to
#   `origin/landing`, and the next reading runs the new script.
# - The detector's checkout takes a landing outside `.config/` and
#   `mise.toml`, and the detector reads on. It takes a landing of a new
#   script, and the detector starts again from it.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watch-reload.XXXXXX")
trap 'rm -rf "$work"' EXIT
export XDG_STATE_HOME=$work/state
# shellcheck source=watch.bash
source "$here/watch.bash"
# The scratch checkouts take no entry in the host's list of trusted configurations.
mise() { :; }
failed=0
fail() {
  echo "watch-reload case FAILED: $1"
  echo "  got: $2"
  failed=1
}

git() { command git -c user.name=case -c user.email=case@example.invalid -c commit.gpgsign=false "$@"; }
git init --quiet --bare --initial-branch=landing "$work/origin.git"
git clone --quiet "$work/origin.git" "$work/seed" 2> /dev/null
mkdir -p "$work/seed/.config/integration"
# Lands a `watch.bash` whose reading prints version `$1`; prints the head.
land() {
  cat > "$work/seed/.config/integration/watch.bash" << EOF
watch_once() { printf '{"repo":"%s","version":$1}\n' "\$1"; }
EOF
  git -C "$work/seed" add .config/integration/watch.bash
  git -C "$work/seed" commit --quiet -m "version $1"
  git -C "$work/seed" push --quiet origin HEAD:landing
  git -C "$work/seed" rev-parse HEAD
}
# Lands a note outside the scripts; prints the head.
land_note() {
  echo "$1" > "$work/seed/NOTES.md"
  git -C "$work/seed" add NOTES.md
  git -C "$work/seed" commit --quiet -m "note $1"
  git -C "$work/seed" push --quiet origin HEAD:landing
  git -C "$work/seed" rev-parse HEAD
}
# One reading as the service runs it: set the checkout, then read.
reading() {
  (cd "$watch_home" && service_home_sync "$watch_home" && watch_dir=$watch_home/.config/integration watch_reading case/case)
}

# The service's checkout stands after a sweep of the lane's worktree.
first=$(land 1)
git clone --quiet "$work/origin.git" "$work/lane"
git -C "$work/lane" worktree add --quiet --detach "$work/lane-worktree" 2> /dev/null
(cd "$work/lane-worktree" && service_home_sync "$watch_home") || fail "#6653: a lane's worktree does not make the service's checkout" "exit $?"
git -C "$work/lane" worktree remove --force "$work/lane-worktree"
# The service's clone links the objects of the lane's repository, and keeps them when that repository goes too.
rm -rf "$work/lane"
got=$(git -C "$watch_home" rev-parse HEAD 2>&1) || :
[[ $got == "$first" ]] || fail "#6653: the service's checkout does not stand after a sweep of the lane's worktree" "$got"
got=$(reading) || :
[[ $got == '{"repo":"case/case","version":1}' ]] || fail "#6653: a reading after the sweep does not run landing's watch.bash" "$got"

# A reading after a new `watch.bash` on landing runs the new script.
second=$(land 2)
got=$(reading) || :
[[ $got == '{"repo":"case/case","version":2}' ]] || fail "#6653: a reading after a new watch.bash on landing does not run the new script" "$got"
got=$(git -C "$watch_home" rev-parse HEAD)
[[ $got == "$second" ]] || fail "#6653: the service's checkout does not take the new head of landing" "$got"

# The detector's checkout reads on over a landing outside its scripts, and
# starts again over a landing of a new script.
(cd "$work/seed" && service_home_sync "$stall_home") || fail "#7002: the seed does not make the detector's checkout" "exit $?"
before=$(git -C "$stall_home" rev-parse HEAD)
noted=$(land_note 1)
service_home_sync "$stall_home" || fail "#7002: the detector's checkout does not take a landing" "exit $?"
got=$(git -C "$stall_home" rev-parse HEAD)
[[ $got == "$noted" ]] || fail "#7002: the detector's checkout does not take the new head of landing" "$got"
if stall_scripts_moved "$before"; then fail "#7002: a landing outside the scripts starts the detector again" "moved from ${before::9}"; fi
before=$got
land 3 > /dev/null
service_home_sync "$stall_home" || fail "#7002: the detector's checkout does not take a landing" "exit $?"
stall_scripts_moved "$before" || fail "#7002: a landing of a new script does not start the detector again" "unmoved from ${before::9}"

(( failed == 0 )) || exit 1
echo "watch-reload check OK: the service's checkout stands after a sweep of a lane's worktree, and a reading after a new watch.bash on landing runs the new script; the detector's checkout reads on over a landing outside its scripts and starts again over a new script"
