#!/usr/bin/env bash
# The head watcher's token (#6644), run by `check:integration`. `watch_token`
# runs over a stubbed gh whose `auth token` gives `read-token`, or fails. With
# no `GH_TOKEN`, the watcher's gate takes the token gh gives, as a seat's gate
# holds one. A token already set stays, and a failed read leaves none.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watch-token.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
cat > "$work/bin/gh" << 'EOF'
#!/usr/bin/env bash
[[ "$*" == "auth token" && -z ${STUB_FAIL:-} ]] || exit 1
echo read-token
EOF
chmod +x "$work/bin/gh"
failed=0
fail() {
  echo "watch-token case FAILED: $1"
  echo "  got: $2"
  failed=1
}
token() {
  env -u GH_TOKEN "$@" PATH="$work/bin:$PATH" XDG_STATE_HOME="$work/state" \
    bash -c 'source "$1"; watch_token; printf "%s\n" "${GH_TOKEN-unset}"' _ "$here/watch.bash" 2> /dev/null
}

got=$(token)
[[ $got == read-token ]] || fail "#6644: with no GH_TOKEN, the watcher's gate takes the token gh gives" "$got"
got=$(token GH_TOKEN=seat-token)
[[ $got == seat-token ]] || fail "#6644: a GH_TOKEN already set stays" "$got"
got=$(token STUB_FAIL=1)
[[ $got == unset ]] || fail "#6644: a failed read leaves GH_TOKEN unset" "$got"

(( failed == 0 )) || exit 1
echo "watch-token check OK: the watcher's gate takes gh's token when it has none, keeps one it has, and takes none from a failed read"
