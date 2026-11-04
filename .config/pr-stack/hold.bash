# The hold on the stack top (#5122), sourced by `stack.bash` and
# `.config/stall/stall.bash`. `pr:open` restacks a branch onto the server's
# top and then refuses it until a gate passes on the new tree. A gate takes 6
# to 35 minutes, and another seat's `pr:open` in that window moves the top
# again, so a seat can lose gate after gate. One `pr:open` at a time holds
# the top from its stacking to its push. Another `pr:open` that finds the top
# held waits for the holder's push, as `pr:await` waits, and does not restack.
#
# The server keeps the hold, because seats on two hosts share one top. It is
# the ref `refs/pr-stack/hold` on `origin`: a commit with no parent and the
# empty tree, its message the record `{holder, head, began, deadline}`, the
# holder a branch and the times epoch seconds. Every write is one push leased
# on the record it read, so of two seats writing at once one wins, and the
# other reads again. The push hooks pass `refs/pr-stack/*`, which carries no
# change. A read is one `ls-remote` and, for a record not seen before, one
# fetch.
#
# A hold stands `top_hold_seconds` past its last write. A holder that crashes
# releases it there: the next `pr:open` takes it over. A `pr:open` of the
# holder renews it, so a hold can outlive the claim window; `stall:watch`
# reports it then (`detect.jq`'s `top-held`).

top_hold_dir="$(git rev-parse --show-toplevel)/.config/pr-stack"
top_hold_ref=refs/pr-stack/hold
# One gate and its restack, with room to spare.
top_hold_seconds=${pr_stack_hold_seconds:-3600}
# The record the running `pr:open` wrote, empty while it holds nothing.
top_hold_sha=

# The hold the server keeps, `{sha, holder, head, began, deadline}`, or
# `null`. Fails when a read fails, or when the record moves between the two
# reads.
top_hold_reading() {
  local sha
  sha=$(git ls-remote origin "$top_hold_ref") || return 1
  sha=${sha%%[[:space:]]*}
  if [[ -z $sha ]]; then
    echo null
    return
  fi
  if ! git cat-file -e "$sha^{commit}" 2> /dev/null; then
    git fetch --quiet --no-write-fetch-head origin "+$top_hold_ref:$top_hold_ref" || return 1
  fi
  git log -1 --format=%B "$sha" 2> /dev/null | jq -c --arg sha "$sha" '. + {sha: $sha}'
}

# Write the hold for branch `$1` at head `$2`, begun at `$3`, over the record
# `$4` the server keeps, empty for none: one push leased on `$4`. Sets
# `top_hold_sha` when the push lands; fails when another write came first.
top_hold_write() {
  local tree record sha
  tree=$(git hash-object -t tree -w /dev/null)
  record=$(jq -cn --arg holder "$1" --arg head "$2" --argjson began "$3" --argjson deadline "$(($(date +%s) + top_hold_seconds))" \
    '{holder: $holder, head: $head, began: $began, deadline: $deadline}')
  sha=$(git -c commit.gpgsign=false commit-tree "$tree" -m "$record")
  git push --quiet --force-with-lease="$top_hold_ref:$4" origin "$sha:$top_hold_ref" 2> /dev/null || return 1
  top_hold_sha=$sha
}

# Hold the stack top for the checked-out branch `$1` at head `$2`
# (`hold.jq`). Returns 0 once it holds the top, printing a line when it took
# over a hold past its deadline. Returns 3 while another branch holds it,
# printing the `wait:` line and the `arm:` line for `pr:await hold`, so the
# seat's turn ends and the job wakes it at the release (#4164). Returns 2,
# naming the reason, when the reading fails or three writes in a row lose.
top_hold_take() {
  local own=$1 head=$2 hold decision began
  for _ in 1 2 3; do
    hold=$(top_hold_reading) || {
      echo "the stack top's hold (\`$top_hold_ref\`) could not be read; run \`pr:open\` again" >&2
      return 2
    }
    decision=$(jq -nc --argjson hold "$hold" --arg own "$own" --argjson now "$(date +%s)" '{hold: $hold, own: $own, now: $now}' \
      | jq -c -f "$top_hold_dir/hold.jq")
    case $(jq -r .act <<< "$decision") in
      wait)
        printf 'wait: %s; its push releases it\n' "$(jq -r .why <<< "$decision")"
        jq -nr -L "$top_hold_dir" 'include "await"; arm("hold")'
        return 3
        ;;
      take) began=$(date +%s) ;;
      renew) began=$(jq -r .began <<< "$decision") ;;
    esac
    if top_hold_write "$own" "$head" "$began" "$(jq -r '.sha // ""' <<< "$hold")"; then
      if [[ $(jq -r '.over // ""' <<< "$decision") != "" ]]; then
        echo "the stack top's hold by \`$(jq -r .over <<< "$decision")\` passed its deadline; $own takes it over"
      fi
      return 0
    fi
  done
  echo "the stack top's hold changed under three writes in a row; run \`pr:open\` again" >&2
  return 2
}

# Release the hold the running `pr:open` wrote (`top_hold_sha`): one push
# that deletes the ref, leased on that record, so a hold another branch took
# over past its deadline stays. Does nothing while it holds nothing.
top_hold_release() {
  [[ -n $top_hold_sha ]] || return 0
  git push --quiet --force-with-lease="$top_hold_ref:$top_hold_sha" origin ":$top_hold_ref" 2> /dev/null || :
  top_hold_sha=
}
