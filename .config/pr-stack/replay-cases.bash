#!/usr/bin/env bash
# The tree check of a signed replay (#6020), run by `check:pr-stack`. Each
# case builds a scratch repository with a local bare origin whose branch `b`
# stands on the base, and a rebased tip one commit past it. `signed_replay`
# then replays the tip through a stub `gh`. The stub carries out
# `createCommitOnBranch` on the origin with git, as GitHub does: a file a
# commit adds comes out `100644`, and `$STUB_SPOIL` names a path whose blob
# the stub replaces. A replay whose tree matches moves `b`. A replay whose
# tree differs leaves `b` and names each differing path with its mode and its
# blob on each side. Only a difference in a mode alone keeps the mode reason.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-replay.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
failed=0

source "$here/../cases/scratch.bash"

fail() {
  printf 'pr-stack replay case %s\n  got: %s\n' "$1" "$2" >&2
  failed=1
}

# The GitHub calls `signed_replay` makes, on the bare origin `$STUB_ORIGIN`.
mkdir "$work/gh"
cat > "$work/gh/gh" << 'STUB'
#!/usr/bin/env bash
set -euo pipefail
origin=${STUB_ORIGIN:?}
[[ $1 == api ]] || { echo "stub gh: $*" >&2; exit 1; }
shift
method=GET input='' path='' fields=()
while (($#)); do
  case $1 in
    --method) method=$2; shift 2 ;;
    --input) input=$2; shift 2 ;;
    --jq) shift 2 ;;
    -f | -F) fields+=("$2"); shift 2 ;;
    *) path=$1; shift ;;
  esac
done
field() { local f; for f in "${fields[@]}"; do [[ $f != "$1="* ]] || echo "${f#*=}"; done; }
commit_on_branch() {
  local request branch head index blob mode path contents tree commit
  request=$(< "$input")
  branch=$(jq -r .variables.input.branch.branchName <<< "$request")
  head=$(git -C "$origin" rev-parse "refs/heads/$branch")
  [[ $head == "$(jq -r .variables.input.expectedHeadOid <<< "$request")" ]] || { echo "stub gh: the head moved" >&2; exit 1; }
  index=$(mktemp -u "${TMPDIR:-/tmp}/gandr-replay-index.XXXXXX")
  export GIT_INDEX_FILE=$index
  git -C "$origin" read-tree "$head"
  while IFS=$'\t' read -r path contents; do
    if [[ $path == "${STUB_SPOIL:-}" ]]; then
      blob=$(printf 'spoiled\n' | git -C "$origin" hash-object -w --stdin)
    else
      blob=$(printf '%s' "$contents" | base64 -d | git -C "$origin" hash-object -w --stdin)
    fi
    mode=$(git -C "$origin" ls-tree "$head" -- "$path" | awk '{ print $1 }')
    git -C "$origin" update-index --add --cacheinfo "${mode:-100644},$blob,$path"
  done < <(jq -r '.variables.input.fileChanges.additions[] | [.path, .contents] | @tsv' <<< "$request")
  while IFS= read -r path; do
    git -C "$origin" update-index --force-remove -- "$path"
  done < <(jq -r '.variables.input.fileChanges.deletions[].path' <<< "$request")
  tree=$(git -C "$origin" write-tree)
  commit=$(git -C "$origin" -c user.name=github -c user.email=github@example.invalid commit-tree "$tree" -p "$head" \
    -m "$(jq -r .variables.input.message.headline <<< "$request")")
  git -C "$origin" update-ref "refs/heads/$branch" "$commit" "$head"
  rm -f "$index"
  echo "$commit"
}
case $method:$path in
  *:rate_limit) echo 0 ;;
  *:graphql) commit_on_branch ;;
  POST:repos/*/git/refs) git -C "$origin" update-ref "$(field ref)" "$(field sha)" ;;
  GET:repos/*/git/ref/heads/*) git -C "$origin" rev-parse "refs/heads/${path#*/git/ref/heads/}" ;;
  PATCH:repos/*/git/refs/heads/*) git -C "$origin" update-ref "refs/heads/${path#*/git/refs/heads/}" "$(field sha)" ;;
  DELETE:repos/*/git/refs/heads/*) git -C "$origin" update-ref -d "refs/heads/${path#*/git/refs/heads/}" ;;
  *) echo "stub gh: $method $path" >&2; exit 1 ;;
esac
STUB
chmod +x "$work/gh/gh"
export PATH="$work/gh:$PATH" GH_BUDGET_TTL=0 XDG_CACHE_HOME="$work/cache"

# A scratch origin at `$1/origin.git` whose `main` and `b` stand on a base,
# and a clone at `$1/clone` on the base, detached, ready for the tip's commit.
setup() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  identity
  commit a.txt base base
  git push --quiet origin main main:b
  base=$(git rev-parse HEAD)
  git switch --quiet --detach
  export STUB_ORIGIN=$1/origin.git
}

# Replay the clone's HEAD as `b`, and read the exit status, the first line on
# stderr, each path line, whether `b` moved and whether the scratch is left.
replay() {
  local status=0 new
  new=$(signed_replay b "$base" HEAD "$base" 2> "$work/err") || status=$?
  printf 'exit %s; %s; paths:%s; b %s; scratch %s' "$status" "$(head -n 1 "$work/err")" \
    "$(sed -E -e '1d' -e 's/^ +//' -e 's/[0-9a-f]{12}/<blob>/g' -e 's/.*/ [&]/' "$work/err" | tr -d '\n')" \
    "$(if [[ $(git -C "$STUB_ORIGIN" rev-parse b) == "$base" ]]; then echo unmoved; elif [[ $(git -C "$STUB_ORIGIN" rev-parse 'b^{tree}') == $(git rev-parse 'HEAD^{tree}') ]]; then echo "moved to the tip's tree"; else echo "moved elsewhere"; fi)" \
    "$(git -C "$STUB_ORIGIN" show-ref --quiet refs/heads/restack/b && echo left || echo deleted)"
}

got=$(
  setup "$work/match"
  commit b.txt own 'own'
  replay
)
[[ $got == "exit 0; ; paths:; b moved to the tip's tree; scratch deleted" ]] || fail "#6020: a replay whose tree matches the rebase moves the branch" "$got"

got=$(
  setup "$work/mode"
  printf '#!/bin/sh\n' > run.sh
  chmod +x run.sh
  git add run.sh
  git commit --quiet -m 'add an executable'
  replay
)
[[ $got == "exit 1; the signed replay of b gives another tree than the rebase: a file it adds keeps no mode; paths: [run.sh: 100755 <blob> in the rebase, 100644 <blob> in the replay]; b unmoved; scratch deleted" ]] \
  || fail "#6020: a replay that differs in a mode alone keeps the mode reason and names the path with both modes" "$got"

got=$(
  setup "$work/blob"
  commit b.txt own 'own'
  printf '#!/bin/sh\n' > run.sh
  chmod +x run.sh
  git add run.sh
  git commit --quiet -m 'add an executable'
  git reset --quiet --soft HEAD~2
  git commit --quiet -m 'own and an executable'
  STUB_SPOIL=b.txt replay
)
[[ $got == "exit 1; the signed replay of b gives another tree than the rebase at these paths; paths: [b.txt: 100644 <blob> in the rebase, 100644 <blob> in the replay] [run.sh: 100755 <blob> in the rebase, 100644 <blob> in the replay]; b unmoved; scratch deleted" ]] \
  || fail "#6020: a replay whose blob differs names each path with its mode and its blob on each side, and no mode reason" "$got"

(( failed == 0 )) || exit 1
echo "pr-stack replay OK: 3 cases move a matching replay, keep the mode reason for a mode alone, and name each path of a blob that differs"
