#!/usr/bin/env bash
# `pr:hold` writes one comment through a stubbed GitHub. Each case records the
# hold state, its reason and the complete Markdown body.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
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
    printf 'false\tfalse\tfalse\n'
    ;;
  label)
    [[ ${2:-} == create ]] || { echo "gh stub: unexpected $*" >&2; exit 1; }
    ;;
  pr)
    case ${2:-} in
      edit|ready) ;;
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
failed=0
count=$(jq length "$cases")
for (( index = 0; index < count; index++ )); do
  name=$(jq -r ".[$index].name" "$cases")
  owner=$(jq -r ".[$index].owner" "$cases")
  number=$(jq -r ".[$index].number" "$cases")
  reason=$(jq -r ".[$index].reason" "$cases")
  expected=$(jq -r ".[$index].body" "$cases")
  comment=$work/comment-$index
  args=()
  [[ $owner != true ]] || args+=(--owner)
  status=0
  output=$(GH_REPO=case/case STUB_HOLD_COMMENT="$comment" PATH="$work/bin:$PATH" \
    MISE_DISABLE_TOOLS="${MISE_DISABLE_TOOLS:+$MISE_DISABLE_TOOLS,}github:cli/cli" \
    mise run --quiet pr:hold "${args[@]}" "$number" "$reason" 2> "$work/err") || status=$?
  got=$(< "$comment")
  if [[ $status != 0 || $got != "$expected" ]]; then
    printf 'hold case FAILED: %s\n  expected (exit 0):\n%s\n  actual (exit %s):\n%s\n' "$name" "$expected" "$status" "$got" >&2
    cat "$work/err" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "hold OK: $count cases write the recorded lead and table"
