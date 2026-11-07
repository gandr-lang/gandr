#!/usr/bin/env bash
# The filings of `issue:file` and `refactor:file` against one GitHub (#5149),
# run by `check:claims` over the cases in `filed-once.json`. The GitHub is the
# stub `filed-once-gh.bash`. The runs come from two clones of the tree under
# test, each with a host lock and a state directory of its own, as two hosts
# have. The runtime directory stays the host's (#6182). A commit of the
# working tree, written through an index of its own, is what the clones check
# out, so a change not yet committed is tested too. The real index and `HEAD`
# do not change.
#
# A case of kind `epic` runs `issue:file --epic 4481` from one clone, over an
# epic that holds the case's `subs` sub-issues. A case of kind `race` runs
# `refactor:file 5` from both clones at once, over a merged pull request #5
# with a `yes` verdict. The result is the exit statuses, the open and closed
# issues on the board, and the links or the closes the runs called, compared
# with the case's `output`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=../mise/disabled-tools.bash
source "$here/../mise/disabled-tools.bash"
disabled=$(disabled_tools github:cli/cli)
root=$(git -C "$here" rev-parse --show-toplevel)
cases=$here/filed-once.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-filed-once.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

index=$work/index
GIT_INDEX_FILE=$index git -C "$root" read-tree HEAD
GIT_INDEX_FILE=$index git -C "$root" add --all
tree=$(GIT_INDEX_FILE=$index git -C "$root" write-tree)
commit=$(git -C "$root" -c user.name=case -c user.email=case@example.invalid commit-tree -p HEAD -m "filed-once: the tree under test" "$tree")
for clone in a b; do
  git clone --quiet --shared --no-checkout "$root" "$work/$clone"
  git -C "$work/$clone" checkout --quiet --detach "$commit"
done

mkdir -p "$work/gh" "$work/config/gandr"
ln -s "$here/filed-once-gh.bash" "$work/gh/gh"
# `body:check` reads the private-names list; this one matches no case's text.
echo '^no case writes this line$' > "$work/config/gandr/private-names"
mise_config=${MISE_CONFIG_DIR:-${XDG_CONFIG_HOME:-$HOME/.config}/mise}
printf '## Observation\n\n|Kind|Where|Observation|\n|---|---|---|\n|generalise|`.config/claims/filing.jq`|two readers walk one board|\n\nfrom: #5\n' > "$work/body.md"
jq -n '{state: "MERGED", headRefName: "triage-7-filed",
  body: "## Refactoring\n\nyes\n\n|Kind|Where|Observation|\n|---|---|---|\n|generalise|`.config/claims/filing.jq`|two readers walk one board|\n",
  closingIssuesReferences: {nodes: [{number: 7, parent: {number: 4481}, labels: {nodes: [{name: "area:workflow"}]}}]}}' > "$work/pr.json"

# Run `$3...` in the clone `$1`, with the host directories of `$2`.
run() {
  local clone=$1 host=$2
  shift 2
  mkdir -p "$work/locks-$host" "$work/state-$host"
  (cd "$work/$clone" && env PATH="$work/gh:$PATH" STUB_GH="$work/stub" STUB_SUBS="$subs" GH_BUDGET_TTL=0 \
    MISE_DISABLE_TOOLS="$disabled" \
    MISE_CONFIG_DIR="$mise_config" MISE_TRUSTED_CONFIG_PATHS="$work/a:$work/b" \
    XDG_CONFIG_HOME="$work/config" GANDR_HOST_LOCK_DIR="$work/locks-$host" XDG_STATE_HOME="$work/state-$host" \
    "$@") > "$work/out-$host" 2>&1
}

while IFS= read -r case; do
  subs=$(jq .subs <<< "$case")
  rm -rf "$work/stub"
  mkdir "$work/stub"
  echo '[]' > "$work/stub/board.json"
  cp "$work/pr.json" "$work/stub/pr.json"
  case $(jq -r .kind <<< "$case") in
    epic)
      status=0
      run a a mise run --quiet issue:file "refactor(workflow): generalise — filing.jq" "$work/body.md" \
        kind:refactor area:workflow status:unsectioned --epic 4481 || status=$?
      links=$(awk 'index($0, "api -X POST repos/{owner}/{repo}/issues/4481/sub_issues") == 1 { n++ } END { print n + 0 }' "$work/stub/calls")
      # Each GitHub read the filing makes (#5709): an `api` call that writes
      # nothing. The free `rate_limit` gauge reads at most once a minute from
      # the host's cache, so the count leaves it out.
      reads=$(awk '/^api / && !/^api -X / && !/^api rate_limit/ { n++ } END { print n + 0 }' "$work/stub/calls")
      last=$(jq -r '.[0].body // "" | split("\n") | map(select(. != "")) | last // ""' "$work/stub/board.json")
      tail="$links links; reads $reads; the body ends \`$last\`"
      statuses=$status
      ;;
    race)
      run a a mise run --quiet refactor:file 5 &
      first=$!
      run b b mise run --quiet refactor:file 5 &
      second=$!
      a=0 b=0
      wait "$first" || a=$?
      wait "$second" || b=$?
      statuses="$a $b"
      tail="closed: $(awk '/^issue close/ { printf "%s`%s`", (n++ ? ", " : ""), $0 }' "$work/stub/calls")"
      ;;
  esac
  board=$(jq -r '"\(map(select(.state == "OPEN")) | length) open, \(map(select(.state == "CLOSED")) | length) closed"' "$work/stub/board.json")
  got="exit $statuses; $board; $tail"
  if [[ $got != "$(jq -r .output <<< "$case")" ]]; then
    printf 'filed-once case FAILED: %s\n  got: %s\n' "$(jq -r .name <<< "$case")" "$got" >&2
    for host in a b; do
      [[ ! -f $work/out-$host ]] || sed "s/^/  $host: /" "$work/out-$host" >&2
    done
    failed=1
  fi
  rm -f "$work"/out-*
done < <(jq -c '.[]' "$cases")
((failed == 0)) || exit 1
echo "filed-once check OK: $(jq length "$cases") cases read as recorded"
