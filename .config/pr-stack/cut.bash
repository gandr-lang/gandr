#!/usr/bin/env bash
# The cut of a red bottom that `stall:watch` runs (#5073, `cut_bottom`), run
# by `check:pr-stack` over the cases in `cut.json`. Each case builds a scratch
# repository with a local bare origin: the red bottom `red` with one commit of
# its own, under an upper and a top with one each. The upper's commit adds a
# file of its own when the case's `upper` is `apart`, and rewrites the red
# branch's file when it is `builds`. Pull requests are numbered red 2, upper 3,
# top 4, in server stack 9, and a required check failed on the red one alone.
# `gh` and `stack_link` are recorded, not run. The server takes every edit,
# and its running runs are one on the upper at its old head and one of a merge
# group of the red one. The result is one line compared with the case's
# `output`: the cut's line, its fields joined by ` / `, and the subjects
# main..<branch> holds for the upper, the top and the red branch; or
# `refused: ` and the refusal's first line, and `, moved` should the refused
# cut have moved a branch; then the `gh` calls and each chain linked.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/cut.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-cut.XXXXXX")
trap 'rm -rf "$work"' EXIT
export XDG_RUNTIME_DIR=$work
repo=case/case
trunk=main
failed=0

source "$here/../cases/scratch.bash"
subjects() { git log --format=%s "origin/main..origin/$1" | paste -sd ',' - | sed 's/,/, /g'; }

# The scratch stack in `$1`, its upper `$2` (`apart` or `builds`).
scenario() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  identity
  commit base.txt base base
  git push --quiet origin main
  git switch --quiet --create red
  commit r.txt red "red's own"
  git switch --quiet --create upper
  if [[ $2 == apart ]]; then commit u.txt upper "upper's own"; else commit r.txt upper "upper's own"; fi
  git switch --quiet --create top
  commit t.txt top "top's own"
  git push --quiet origin red upper top
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  dir=$work/$i
  mkdir "$dir"
  scenario "$dir" "$(jq -r ".[$i].upper" "$cases")"
  cd "$dir/clone"
  : > "$dir/gh"
  : > "$dir/link"
  old=$(git rev-parse origin/upper)
  gh() {
    case "$*" in
      "api repos/case/case/actions/runs?status=in_progress"*)
        jq -cn --arg old "$old" '{id: 11, event: "pull_request", head_branch: "upper", head_sha: $old, status: "in_progress"},
          {id: 12, event: "merge_group", head_branch: "gh-readonly-queue/main/pr-2-abc", head_sha: "abc", status: "in_progress"},
          {id: 13, event: "pull_request", head_branch: "elsewhere", head_sha: "def", status: "in_progress"}'
        ;;
      "api repos/case/case/actions/runs?status="*) ;;
      *) printf '%s\n' "$*" >> "$dir/gh" ;;
    esac
  }
  red_reading() {
    if [[ $1 == 2 ]]; then jq -cn '{check: "test the workspace", run: "https://example.invalid/runs/1"}'; else echo null; fi
  }
  # `cut_bottom`'s own `stack` shadows a variable of that name.
  members_json='[{"number":2,"head":"red"},{"number":3,"head":"upper"},{"number":4,"head":"top"}]'
  server_stack() { printf '%s\n' "$members_json"; }
  queued_of() { echo '[]'; }
  stack_of() { if grep -q '^stack unstack' "$dir/gh"; then echo null; else echo 9; fi; }
  pr_reading() { jq -n -c --arg base "$(sed -n 's/^pr edit .* --base //p' "$dir/gh" | tail -n 1)" '{baseRefName: $base}'; }
  stack_link() { jq -r 'map(.number) | join(" ")' <<< "$1" >> "$dir/link"; }
  before=$(git rev-parse origin/upper origin/top origin/red)
  if line=$(cut_bottom 2 2> "$dir/out"); then
    actual="cut: ${line//$'\t'/ / }; upper holds $(subjects upper); top holds $(subjects top); red holds $(subjects red)"
  else
    actual="refused: $(head -n 1 "$dir/out")"
    git fetch --quiet origin
    [[ $(git rev-parse origin/upper origin/top origin/red) == "$before" ]] || actual+=", moved"
  fi
  actual+="; gh: $(paste -sd '|' "$dir/gh" | sed 's/|/ | /g'); link: $(paste -sd '|' "$dir/link" | sed 's/|/ | /g')"
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack cut case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack cut OK: $count cases cut a red bottom as recorded"
