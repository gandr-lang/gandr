#!/usr/bin/env bash
# An invalid cases file stops before the runner starts its absent program.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
fail() {
  printf 'cases check FAILED: %s\n' "$1" >&2
  exit 1
}
refuse() {
  local cases=$1
  local reading=$2
  local stderr="$scratch/stderr"
  local status
  if "$here/run.bash" cases "$cases" --program "$scratch/absent.jq" > /dev/null 2> "$stderr"; then
    status=0
  else
    status=$?
  fi
  (( status == 2 )) || fail "#5646: $reading exits $status, not 2"
  [[ $(< "$stderr") == *"$cases"* ]] || fail "#5646: $reading error does not name it"
}
malformed="$scratch/malformed.json"
not_array="$scratch/not-array.json"
printf '[\n  { "name": "before" }\n  }\n]\n' > "$malformed"
printf '{}\n' > "$not_array"
refuse "$malformed" "a malformed cases file"
refuse "$not_array" "a non-array cases file"
# Each case harness that commits calls `identity` (#7180). The check refuses
# a scratch harness that commits with the host's configuration, names its
# line, and admits one that calls `identity`.
"$here/identity.bash" || fail "#7180: a case harness above commits with no scratch identity"
printf '%s\n' 'set -euo pipefail' 'git init -q "$1"' '# git commit in a comment holds no call' \
  'git -C "$1" -c user.name=x commit -q --allow-empty -m one' > "$scratch/bare-cases.bash"
printf '%s\n' 'source "$here/../cases/scratch.bash"' 'git init -q "$1"' 'identity "$1"' \
  'git -C "$1" commit -q --allow-empty -m one' > "$scratch/kept-cases.bash"
if "$here/identity.bash" "$scratch/bare-cases.bash" 2> "$scratch/stderr"; then
  fail "#7180: a harness that commits with no identity is admitted"
fi
[[ $(< "$scratch/stderr") == *"$scratch/bare-cases.bash:4 "* ]] \
  || fail "#7180: the refusal names no line 4 of the harness: $(< "$scratch/stderr")"
"$here/identity.bash" "$scratch/kept-cases.bash" \
  || fail "#7180: a harness that calls identity is refused"
echo "cases check OK: runner refuses 2 invalid cases files before it runs a program, and each case harness that commits calls identity"
