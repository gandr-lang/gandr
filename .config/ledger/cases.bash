#!/usr/bin/env bash
# The cases of `check:ledger`'s issue reads (#4018). A scratch repository
# holds a ledger of two rows: `gap`, implemented with no witness and resting
# on #1, and `owing`, partial with its own exemplar owing on #2. For each
# case in `.config/ledger/cases.json` a stub `gh` answers the one GraphQL
# query of aliases the check sends: every issue it names answered from the
# case, or the whole read failed as a rate limit does when any is missing
# (#4263). A case's `closes` are `Closes` lines of a commit on the branch,
# its `body` the pull request's body as `pr:open` gives it, its `bodies` the
# bodies of a merge group's entries in the directory the queue gives (#6883),
# and its `event` the body as a pull request's CI event holds it (#6767).
# `check.bash` runs there, and its exit status and standard error are the
# case's. The base of the change that a gate names is not the scratch
# repository's, so the harness drops it.
set -euo pipefail
# The scratch repository's git reads no identity from the host, as the CI
# image has none, and guesses none: a commit that names no author fails
# here as it fails there (#6184).
unset GIT_AUTHOR_NAME GIT_AUTHOR_EMAIL GIT_COMMITTER_NAME GIT_COMMITTER_EMAIL
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=user.useConfigOnly GIT_CONFIG_VALUE_0=true
root=$PWD
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
repo="$scratch/repo"
mkdir -p "$repo/ledger" "$repo/crates/x" "$repo/corpus/ledger/features" "$scratch/gh" "$scratch/answers"
git init --quiet "$repo"
{
  awk '/^CREATE TABLE feature\(/,/\) WITHOUT ROWID;$/' ledger/features.sql
  echo "INSERT INTO feature VALUES('gap','workflow','A gap',NULL,'implemented','ordinary',NULL,'A row with no witness.','x',NULL,NULL,'#1',NULL);"
  echo "INSERT INTO feature VALUES('owing','workflow','An owing row',NULL,'partial','ordinary',NULL,'A partial row.','x',NULL,'corpus/ledger/features/owing.gandr','#2',NULL);"
} | sqlite3 -bail "$scratch/features.db"
sqlite3 "$scratch/features.db" .dump > "$repo/ledger/features.sql"
printf '%s\n' '/// `owing`' '/// Implemented: the row.' '/// Not implemented: the rest.' '///' '/// - owes: #2' 'package owing {}' \
  > "$repo/corpus/ledger/features/owing.gandr"
git -C "$repo" add .
git -C "$repo" -c user.name=ledger -c user.email=ledger@example.invalid -c commit.gpgSign=false \
  commit --quiet -m 'chore(repo): ledger base'
base=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" update-ref refs/remotes/origin/landing "$base"
# Each case's stub answers differently: no reading is kept between them.
export GH_BUDGET_TTL=0
cat > "$scratch/gh/gh" <<'STUB'
#!/usr/bin/env bash
# `gh api graphql -f query=<q> --jq <filter>`: answer each `nN: issue(number: N)`
# alias from $STUB_GH/N (`<state>\t<gap>`), the gap a `kind:gap` label; any
# alias without an answer fails the read as a rate limit does.
query= filter=
while (( $# )); do
  case $1 in
    query=*) query=${1#query=} ;;
    --jq) filter=$2; shift ;;
  esac
  shift
done
entries=()
for n in $(grep -oE 'number: [0-9]+' <<< "$query" | tr -dc '0-9\n'); do
  [[ -f $STUB_GH/$n ]] || { echo "HTTP 403: API rate limit exceeded" >&2; exit 1; }
  IFS=$'\t' read -r state gap < "$STUB_GH/$n"
  labels='[]'; [[ $gap == true ]] && labels='[{"name":"kind:gap"}]'
  entries+=("\"n$n\": {\"state\": \"$state\", \"labels\": {\"nodes\": $labels}}")
done
printf '{"data":{"repository":{%s}}}' "$(IFS=,; printf '%s' "${entries[*]}")" | jq -r "$filter"
STUB
chmod +x "$scratch/gh/gh"
failed=0
while IFS= read -r case; do
  rm -f "$scratch/answers"/*
  git -C "$repo" reset --quiet --hard "$base"
  closes=$(jq -r '.closes[]? | "Closes #\(.)"' <<< "$case")
  if [[ -n $closes ]]; then
    git -C "$repo" -c user.name=ledger -c user.email=ledger@example.invalid -c commit.gpgSign=false \
      commit --quiet --allow-empty \
      -m 'test(ledger): closing issue' -m "$closes"
  fi
  for number in $(jq -r '.answers | keys[]' <<< "$case"); do
    jq -r --arg n "$number" '.answers[$n]' <<< "$case" > "$scratch/answers/$number"
  done
  status=0
  env=(PATH="$scratch/gh:$PATH" STUB_GH="$scratch/answers")
  if jq -e 'has("body")' <<< "$case" > /dev/null; then
    jq -r .body <<< "$case" > "$scratch/body.md"
    env+=(LEDGER_BODY="$scratch/body.md")
  fi
  if jq -e 'has("bodies")' <<< "$case" > /dev/null; then
    rm -rf "$scratch/bodies" && mkdir "$scratch/bodies"
    for index in $(jq -r '.bodies | keys[]' <<< "$case"); do
      jq -r --argjson i "$index" '.bodies[$i]' <<< "$case" > "$scratch/bodies/$((index + 1)).md"
    done
    env+=(LEDGER_BODY="$scratch/bodies")
  fi
  if jq -e 'has("event")' <<< "$case" > /dev/null; then
    jq -c '{pull_request: {body: .event}}' <<< "$case" > "$scratch/event.json"
    env+=(GITHUB_EVENT_PATH="$scratch/event.json")
  fi
  (cd "$repo" && env -u LEDGER_BODY -u GITHUB_EVENT_PATH -u GATE_BASE "${env[@]}" "$root/.config/ledger/check.bash") \
    > /dev/null 2> "$scratch/err" || status=$?
  if [[ $status != $(jq .exit <<< "$case") || $(< "$scratch/err") != $(jq -r .stderr <<< "$case") ]]; then
    printf 'ledger case FAILED: %s\n  exit %s, wanted %s\n  stderr:\n%s\n' \
      "$(jq -r .name <<< "$case")" "$status" "$(jq .exit <<< "$case")" "$(< "$scratch/err")" >&2
    failed=1
  fi
done < <(jq -c '.[]' .config/ledger/cases.json)
(( failed == 0 )) || exit 1
echo "ledger cases OK: $(jq length .config/ledger/cases.json) cases read their issues as recorded"
