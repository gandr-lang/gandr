#!/usr/bin/env bash
# `pr:await`'s poll over a stubbed `gh` (#4803), run by `check:pr-stack` once
# per case in `await.json`: the repository is `case/case`, the awaited number
# 7, the host's reading of the open pull requests holds none (#5061), and
# the issue read answers the case's `issue`, or fails when it is
# `fail`. The wait runs with `--timeout 0`, so it reads once and ends on that
# reading's event or at the deadline. The result is the wait's stdout and exit
# status, compared with the case's `output` and `status`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=../mise/disabled-tools.bash
source "$here/../mise/disabled-tools.bash"
disabled=$(disabled_tools github:cli/cli)
cases=$here/await.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-await.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
# Each case's stub answers differently: no reading is kept between them.
export GH_BUDGET_TTL=0
export GH_REPO=case/case
cat > "$work/bin/gh" << 'EOF'
#!/usr/bin/env bash
case "$*" in
  "api graphql --paginate "*) ;;
  "api repos/case/case/issues/7")
    [[ $AWAIT_ISSUE != fail ]] || { echo 'gh: HTTP 502' >&2; exit 1; }
    printf '%s\n' "$AWAIT_ISSUE"
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
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  status=0
  output=$(AWAIT_ISSUE=$(jq -r ".[$i].issue" "$cases") PATH="$work/bin:$PATH" XDG_STATE_HOME="$work/state" \
    MISE_DISABLE_TOOLS="$disabled" \
    mise run --quiet pr:await 7 --timeout 0 2> "$work/err") || status=$?
  if [[ $output != "$(jq -r ".[$i].output" "$cases")" || $status != "$(jq -r ".[$i].status" "$cases")" ]]; then
    printf 'pr-stack await case %s\n  expected: %s, exit %s\n  actual:   %s, exit %s\n' "$name" \
      "$(jq -r ".[$i].output" "$cases")" "$(jq -r ".[$i].status" "$cases")" "$output" "$status" >&2
    sed 's/^/    /' "$work/err" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack await OK: $count cases end the wait as recorded"
