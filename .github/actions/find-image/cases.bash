#!/usr/bin/env bash
# `lookup.sh` reads a tag as published only when the registry serves its
# index and every manifest the index lists (#5128), run by `check:find-image`
# over a `docker` stub. The stub answers `docker manifest inspect <ref>` from
# a fixture directory: `<ref>.json` is a manifest the registry serves, and
# `<ref>.err` an error it answers; a ref with neither answers `manifest
# unknown`. Each case writes its fixtures and gives the line `lookup.sh`
# prints, or `fails` when it exits non-zero.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-find-image.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0
count=0
image=ghcr.io/gandr-lang/gandr-ci:tag
repo=ghcr.io/gandr-lang/gandr-ci
index='{"manifests":[{"digest":"sha256:arm","platform":{"architecture":"arm64"}},{"digest":"sha256:amd","platform":{"architecture":"amd64"}}]}'

cat > "$work/docker" << 'STUB'
#!/usr/bin/env bash
ref=$3
key=${ref//[\/:@]/_}
if [[ -f "$FIXTURES/$key.json" ]]; then
  cat "$FIXTURES/$key.json"
elif [[ -f "$FIXTURES/$key.err" ]]; then
  cat "$FIXTURES/$key.err" >&2
  exit 1
else
  echo 'manifest unknown' >&2
  exit 1
fi
STUB
chmod +x "$work/docker"

serve() { printf '%s' "$2" > "$FIXTURES/${1//[\/:@]/_}.json"; }
refuse() { printf '%s\n' "$2" > "$FIXTURES/${1//[\/:@]/_}.err"; }

run_case() {
  local name=$1 expected=$2 actual
  count=$((count + 1))
  if actual=$(DOCKER="$work/docker" "$here/lookup.sh" "$image" 2> "$FIXTURES/stderr"); then :; else actual=fails; fi
  if [[ $actual != "$expected" ]]; then
    printf 'find-image case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$FIXTURES/stderr" >&2
    failed=1
  fi
}

fixtures() { export FIXTURES=$work/$1; mkdir -p "$FIXTURES"; }

fixtures whole
serve "$image" "$index"
serve "$repo@sha256:arm" '{}'
serve "$repo@sha256:amd" '{}'
run_case "a tag whose index and both manifests the registry serves is published" found=true

fixtures gone
serve "$image" "$index"
serve "$repo@sha256:amd" '{}'
run_case "#5128: a tag whose index lists an arm64 manifest the registry does not serve is missing" found=false

fixtures absent
run_case "a tag the registry does not know is missing" found=false

fixtures broken
refuse "$image" 'denied: permission_denied: read_package'
run_case "a registry error on the tag fails the lookup" fails

fixtures broken-manifest
serve "$image" "$index"
refuse "$repo@sha256:arm" 'Get "https://ghcr.io/v2/": net/http: TLS handshake timeout'
run_case "a registry error on a listed manifest fails the lookup" fails

(( failed == 0 )) || exit 1
echo "find-image check OK: $count cases read as recorded"
