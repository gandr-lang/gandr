#!/usr/bin/env bash
# The landing App's installation token for this repository (#2706), minted
# without a third-party action: the repository's Actions allowlist admits
# none that does it, and `actions/create-github-app-token` is refused at
# startup. GitHub's own recipe: a JSON Web Token signed RS256 with the App's
# private key, issued by the App and valid for nine minutes, exchanged for an
# installation token scoped to this repository and to the permissions the
# watcher uses.
#
# Environment: `LANDING_APP_ID` (the App's client ID or numeric ID, the JWT's
# issuer), `LANDING_APP_PRIVATE_KEY` (its PEM private key), `GITHUB_REPOSITORY`.
# Masks the token in the run's log and writes it to `GITHUB_OUTPUT` as
# `token`.
set -euo pipefail
: "${LANDING_APP_ID:?}" "${LANDING_APP_PRIVATE_KEY:?}" "${GITHUB_REPOSITORY:?}"
api=${GITHUB_API_URL:-https://api.github.com}
b64url() { openssl base64 -A | tr '+/' '-_' | tr -d '='; }
now=$(date +%s)
header=$(printf '{"alg":"RS256","typ":"JWT"}' | b64url)
claims=$(jq -cn --arg iss "$LANDING_APP_ID" --argjson now "$now" \
  '{iat: ($now - 60), exp: ($now + 540), iss: ($iss | if test("^[0-9]+$") then tonumber else . end)}' | b64url)
key=$(mktemp)
trap 'rm -f "$key"' EXIT
printf '%s\n' "$LANDING_APP_PRIVATE_KEY" > "$key"
signature=$(printf '%s.%s' "$header" "$claims" | openssl dgst -sha256 -sign "$key" -binary | b64url)
jwt="$header.$claims.$signature"
call() {
  curl --fail-with-body --silent --show-error -H "Authorization: Bearer $jwt" \
    -H 'Accept: application/vnd.github+json' -H 'X-GitHub-Api-Version: 2022-11-28' "$@"
}
installation=$(call "$api/repos/$GITHUB_REPOSITORY/installation" | jq -r .id)
token=$(call -X POST "$api/app/installations/$installation/access_tokens" \
  -d "$(jq -cn --arg repo "${GITHUB_REPOSITORY#*/}" '{repositories: [$repo], permissions: {contents: "write", pull_requests: "write", merge_queues: "write", issues: "write", checks: "read", statuses: "read"}}')" \
  | jq -r .token)
[[ -n $token && $token != null ]] || { echo 'the landing App issued no installation token' >&2; exit 1; }
echo "::add-mask::$token"
printf 'token=%s\n' "$token" >> "$GITHUB_OUTPUT"
