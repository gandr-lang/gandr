# shellcheck shell=bash
# The brake's reading (#5442), which `ci:brake` and `ci:cycle` source.
# `brake_read <runs>` prints the output of `brake.jq`. The file `runs` holds
# the newest dispatched runs of ci.yml on `integration`, as the caller read
# them. The lag in hours comes from git with no API call: the checkout
# fetches the commits of the whole history, with `origin/main` and
# `origin/landing` as they stand at the checkout. A local run reads the refs
# of its last fetch. A history with no common commit of the two cannot give
# the lag, as in a checkout of one commit, so the reading fails. A failed
# reading holds the landings.
brake_read() {
  local runs=$1 here oldest
  here=$(git rev-parse --show-toplevel)/.config/integration
  if ! git merge-base refs/remotes/origin/main refs/remotes/origin/landing > /dev/null; then
    echo "brake: the history holds no common commit of main and landing, so it gives no lag" >&2
    return 1
  fi
  # A command substitution does not inherit `set -e`, so each failure
  # returns at once and never reads as a lag of nothing.
  oldest=$(git log --first-parent --format=%ct refs/remotes/origin/main..refs/remotes/origin/landing | tail -n 1) || return 1
  jq -n -c --argjson now "$(date +%s)" --argjson oldest "${oldest:-null}" --slurpfile runs "$runs" \
    --slurpfile limits "$here/brake.json" '{now: $now, oldest: $oldest, runs: $runs[0], limits: $limits[0]}' \
    | jq -c -L "$here" -f "$here/brake.jq"
}
