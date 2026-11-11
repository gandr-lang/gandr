#!/usr/bin/env bash
# `pr:hold` writes one comment through a stubbed GitHub. Each case records the
# hold state, its reason and the complete Markdown body. A case with a null
# body is a refusal: exit 2, and no write reaches GitHub (#5902). The stub
# holds no open pull request, so the held one stands in no stack.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=../mise/disabled-tools.bash
source "$here/../mise/disabled-tools.bash"
disabled=$(disabled_tools github:cli/cli)
cases=$here/hold.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-hold.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
cat > "$work/bin/gh" << 'EOF'
#!/usr/bin/env bash
set -euo pipefail
case "$1" in
  repo)
    [[ ${2:-} == view ]] || { echo "gh stub: unexpected $*" >&2; exit 1; }
    printf '%s\n' case/case
    ;;
  api)
    [[ ${2:-} == graphql ]] || { echo "gh stub: unexpected $*" >&2; exit 1; }
    # The read of every open pull request finds none.
    [[ $* == *'pullRequests('* ]] || printf '%s\tfalse\tfalse\tfalse\n' "$STUB_HOLD_STATE"
    ;;
  label)
    [[ ${2:-} == create ]] || { echo "gh stub: unexpected $*" >&2; exit 1; }
    echo "$*" >> "$STUB_HOLD_WRITES"
    ;;
  pr)
    case ${2:-} in
      edit|ready) echo "$*" >> "$STUB_HOLD_WRITES" ;;
      comment)
        shift 2
        while (( $# > 0 )); do
          if [[ $1 == --body ]]; then
            printf '%s' "$2" > "$STUB_HOLD_COMMENT"
            exit 0
          fi
          shift
        done
        echo 'gh stub: comment body is missing' >&2
        exit 1
        ;;
      *) echo "gh stub: unexpected $*" >&2; exit 1 ;;
    esac
    ;;
  *) echo "gh stub: unexpected $*" >&2; exit 1 ;;
esac
EOF
chmod +x "$work/bin/gh"
# The stub reads no token. A host can put a `gh` wrapper first on `PATH`,
# and with no `GH_TOKEN` that wrapper asks the next `gh`, the stub, for one
# (#6632). So the case sets a token of its own.
export GH_TOKEN=case
failed=0
count=$(jq length "$cases")
for (( index = 0; index < count; index++ )); do
  name=$(jq -r ".[$index].name" "$cases")
  owner=$(jq -r ".[$index].owner" "$cases")
  number=$(jq -r ".[$index].number" "$cases")
  reason=$(jq -r ".[$index].reason" "$cases")
  state=$(jq -r ".[$index].state // \"OPEN\"" "$cases")
  refused=$(jq ".[$index].body == null" "$cases")
  expected=$(jq -r ".[$index].body // \"\"" "$cases")
  comment=$work/comment-$index
  writes=$work/writes-$index
  : > "$comment"
  : > "$writes"
  args=()
  [[ $owner != true ]] || args+=(--owner)
  status=0
  output=$(GH_REPO=case/case STUB_HOLD_COMMENT="$comment" STUB_HOLD_WRITES="$writes" STUB_HOLD_STATE="$state" PATH="$work/bin:$PATH" \
    MISE_DISABLE_TOOLS="$disabled" \
    mise run --quiet pr:hold "${args[@]}" "$number" "$reason" 2> "$work/err") || status=$?
  got=$(< "$comment")
  if [[ $refused == true ]]; then
    want=2
    [[ $status == 2 && -z $got && ! -s $writes ]] || bad=1
  else
    want=0
    [[ $status == 0 && $got == "$expected" ]] || bad=1
  fi
  if [[ ${bad:-0} == 1 ]]; then
    printf 'hold case FAILED: %s\n  expected (exit %s):\n%s\n  actual (exit %s):\n%s\n  writes:\n%s\n' "$name" "$want" "$expected" "$status" "$got" "$(< "$writes")" >&2
    cat "$work/err" >&2
    failed=1
  fi
  bad=0
done
(( failed == 0 )) || exit 1
echo "hold OK: $count cases write the recorded lead and table, or refuse with no write"
