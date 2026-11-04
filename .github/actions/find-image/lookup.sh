#!/usr/bin/env bash
# Whether the registry publishes the image `$1` whole, as one `found=` line
# for `$GITHUB_OUTPUT`: `true` when it serves the tag's index and every
# manifest the index lists, `false` when it answers `manifest unknown` or
# `not found` for any of them. A pull reads the index and then its platform's
# manifest by digest, so an index whose manifest is gone is missing to the
# jobs, and the run builds the tag again. Any other error fails the lookup,
# so a broken registry fails the image reference rather than silently
# selecting the bare runner or rebuilding. `DOCKER` names the client, a stub
# in `cases.bash`.
set -euo pipefail
image=${1:?the image reference}
docker=${DOCKER:-docker}

missing() { [[ $1 == *"manifest unknown"* || $1 == *"not found"* ]]; }

# The JSON on stdout, any error on stderr.
inspect() {
  local out
  if out=$("$docker" manifest inspect "$1" 2> "$err"); then
    printf '%s' "$out"
  else
    return 1
  fi
}

err=$(mktemp)
trap 'rm -f "$err"' EXIT
if ! index=$(inspect "$image"); then
  if missing "$(< "$err")"; then
    echo "lookup: $image is missing: $(< "$err")" >&2
    echo found=false
    exit 0
  fi
  cat "$err" >&2
  exit 1
fi
repository=${image%:*}
while IFS= read -r digest; do
  [[ -n $digest ]] || continue
  if ! inspect "$repository@$digest" > /dev/null; then
    if missing "$(< "$err")"; then
      echo "the tag's index lists $digest, which the registry does not serve" >&2
      echo found=false
      exit 0
    fi
    cat "$err" >&2
    exit 1
  fi
done < <(jq -r '.manifests[]?.digest' <<< "$index")
echo "lookup: $image is published, its index and the $(jq '[.manifests[]?] | length' <<< "$index") manifests it lists served" >&2
echo found=true
