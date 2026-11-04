#!/usr/bin/env bash
# `epic:deps` over a stubbed `gh` (#4903), run by `check:claims` once per case
# in `epic-deps.json`: the repository is `case/case` and the epic #7, whose
# open sub-issues are the case's `children`, none set yet. Setting a child in
# `refused` fails as GitHub refuses a cycle. The result is the run's stdout,
# one line each, and its exit status, compared with `output` and `status`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
cases=$here/epic-deps.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-epic-deps.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
# Each case's stub answers differently: no reading is kept between them.
export GH_BUDGET_TTL=0
cat > "$work/bin/gh" << 'EOF'
#!/usr/bin/env bash
case "$*" in
  "api --paginate repos/case/case/issues/7/sub_issues?per_page=100 --jq "*)
    jq -c 'map({number: ., state: "open"})' <<< "$EPIC_CHILDREN" ;;
  "api --paginate repos/case/case/issues/7/dependencies/blocked_by?per_page=100 --jq "*) echo '[]' ;;
  "api repos/case/case/issues/"*" --jq .id")
    n=${2#repos/case/case/issues/}
    echo "10$n" ;;
  "api -X POST repos/case/case/issues/7/dependencies/blocked_by -F issue_id=10"*)
    n=${6#issue_id=10}
    if jq -e --argjson n "$n" 'index($n) != null' <<< "$EPIC_REFUSED" > /dev/null; then
      echo 'gh: Validation failed: this dependency would create a cycle where the target is already blocked by the source (HTTP 422)' >&2
      exit 1
    fi
    echo '{}' ;;
  *) echo "gh stub: unexpected $*" >&2; exit 1 ;;
esac
EOF
chmod +x "$work/bin/gh"
failed=0
count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  status=0
  output=$(EPIC_CHILDREN=$(jq -c ".[$i].children" "$cases") EPIC_REFUSED=$(jq -c ".[$i].refused" "$cases") \
    GH_REPO=case/case PATH="$work/bin:$PATH" \
    MISE_DISABLE_TOOLS="${MISE_DISABLE_TOOLS:+$MISE_DISABLE_TOOLS,}github:cli/cli" \
    mise run --quiet epic:deps 7 2> "$work/err") || status=$?
  expected=$(jq -r ".[$i].output[]" "$cases")
  if [[ $output != "$expected" || $status != "$(jq -r ".[$i].status" "$cases")" ]]; then
    printf 'epic-deps case FAILED: %s\n  expected (exit %s):\n%s\n  actual (exit %s):\n%s\n' "$name" \
      "$(jq -r ".[$i].status" "$cases")" "$expected" "$status" "$output" >&2
    sed 's/^/    /' "$work/err" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "epic-deps OK: $count cases set and refuse as recorded"
