#!/usr/bin/env bash
# The sign-off of a unit at the frame now (#7018, `frame.bash`), run by
# `check:claims` over a stub `gh` that records its arguments.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
source "$here/frame.bash"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
failed=0

fail() {
  echo "frame case FAILED: $1"
  echo "  got: $2"
  failed=1
}

mkdir "$dir/bin"
cat > "$dir/bin/gh" << 'EOF'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$GH_ARGS"
EOF
chmod +x "$dir/bin/gh"

frame=$(unit_frame "$root")
signed=$(PATH="$dir/bin:$PATH" GH_ARGS="$dir/args" unit_frame_signoff "$root" 7129 "issue:file")
args=$(< "$dir/args")
[[ $signed == "$frame" ]] || fail "#7129: the sign-off prints the frame now" "$signed"
[[ $args == *"issue"$'\n'"comment"$'\n'"7129"$'\n'"--body"$'\n'"<!-- signed frame=$frame -->"* ]] \
  || fail "#7129: the sign-off comments the marker of the frame now on the issue" "$args"
[[ $args == *'issue:file signs the sections at the unit frame'* ]] \
  || fail "#7129: the sign-off names its signer" "$args"

(( failed == 0 )) || exit 1
echo "frame check OK: 3 cases sign at the frame now"
