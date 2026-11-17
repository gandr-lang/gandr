#!/usr/bin/env bash
# Reads the architect's sign-off of each named override. A body's
# `prose-override:` line admits the paragraphs of a mechanical change only
# when a comment signs it. That comment is on an issue that the body works,
# names the line's substitution and says `signed`.
# - see: #7621
#
# The comment comes from a login of the signers file, with the heading that
# the login's comments hold, as for a deletion. The signers are the factory's
# state and not the tree's. So they live in the configuration directory. A
# body with no override needs no signers and reads no comment.
# - see: `.config/deletes/check.bash`, `$XDG_CONFIG_HOME/gandr/architects.txt`
#
# Usage: signed.bash <body>...
# Prints each override that no sign-off holds and exits 1. Exits 2 when it
# cannot read the signers or the comments.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
architects="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/architects.txt"
status=0
# The signers and the comments go to jq in files: the comments have no
# bound on their size.
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
for body in "$@"; do
  # The override lines outside a fenced block, as the binary reads them.
  mapfile -t lines < <(awk '/^[[:space:]]*```/ { fenced = !fenced; next } !fenced && /^[[:space:]]*prose-override:/ { sub(/^[[:space:]]+/, ""); print }' "$body")
  ((${#lines[@]})) || continue
  [[ -f $architects ]] || {
    echo "check:prose: no signers at $architects: write each login that signs an override there, one a line, then the heading its comment must hold (#7621)" >&2
    exit 2
  }
  source "$root/.config/gh/repo.bash"
  source "$root/.config/gh/budget.bash"
  repo=$(repo_name)
  jq -Rn -c '[inputs | select(test("^[^#]")) | capture("^(?<login>\\S+)\\s*(?<heading>.*)$") | {(.login): .heading}] | add // {}' "$architects" > "$scratch/signers.json"
  mapfile -t issues < <(jq -Rrs -L "$root/.config/bodies" 'include "targets"; targets(working) | unique[]' "$body")
  for issue in "${issues[@]}"; do
    gh api --paginate "repos/$repo/issues/$issue/comments?per_page=100" \
      --jq '.[] | select(.body | test("\\bsigned\\b")) | {author: .user.login, body}' \
      || { echo "check:prose: the comments of #$issue cannot be read" >&2; exit 2; }
  done > "$scratch/comments.jsonl"
  for line in "${lines[@]}"; do
    # The substitution: the old text and the new, each in backticks.
    change=$(sed -E 's/^prose-override:[[:space:]]*mechanical[[:space:]]+(`[^`]*`[[:space:]]*->[[:space:]]*`[^`]*`).*$/\1/' <<< "$line")
    held=$(jq -n -L "$root/.config/bodies" -L "$root/.config/deletes" --slurpfile comments "$scratch/comments.jsonl" --slurpfile signers "$scratch/signers.json" --arg change "$change" \
      'include "account"; $signers[0] as $architects | [$comments[] | select(signer(.; $architects) and (.body | contains($change)))] | length')
    if ((held == 0)); then
      echo "$body: the override \`$line\` has no sign-off: a comment of the architect on the unit names $change and says \`signed\` (#7621)"
      status=1
    fi
  done
done
exit "$status"
