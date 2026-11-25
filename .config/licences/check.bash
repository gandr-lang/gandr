#!/usr/bin/env bash
# The licences of the tree that `cargo-deny` does not read. `check:licences`
# runs this check. `cargo-deny` reads the manifests of ours and the crates of
# the lock file, and this check reads the rest:
#
# - each licence file by its name, anywhere in the tree: `LICENSE`,
#   `LICENCE`, `COPYING`, `NOTICE` and `UNLICENSE`, with any suffix after a
#   `.`, `-` or `_`, in any case, and each file in a `LICENSES` directory. A
#   file passes when the owner's list holds its SHA-256 digest, wherever the
#   file stands, so a new copy of an approved file passes.
# - each SPDX line of a source. A line passes when each licence of its
#   expression is in the allow list of `deny.toml`.
#
# The owner alone widens his list and `deny.toml`, by a code owner's review.
# A refusal names the licence, the place where it comes in and that the owner
# alone approves it. The check reads the tracked files and no network.
# - see: #7743, `.config/licences/approved.json`, `.github/CODEOWNERS`,
#   `deny.toml`, `check:deny`
#
# Usage: check.bash [<root>]
set -euo pipefail
root=${1:-$(git rev-parse --show-toplevel)}
cd "$root"
list=.config/licences/approved.json
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
owner="the owner alone approves a licence, by a code owner's review of $list or deny.toml"

[[ -f $list ]] || { echo "check:licences: no $list, so no licence is approved; $owner" >&2; exit 1; }
jq -e '(.files | type) == "object"' "$list" > /dev/null \
  || { echo "check:licences: $list does not hold the object files" >&2; exit 1; }
yq -p toml -o json '.licenses.allow // []' deny.toml > "$scratch/allow.json" \
  || { echo "check:licences: deny.toml does not parse, so no licence is approved; $owner" >&2; exit 1; }

# The licence files: one line of a digest and a path each.
names=()
for name in licence license copying notice unlicense; do
  names+=(":(glob,icase)**/$name" ":(glob,icase)**/$name.*" ":(glob,icase)**/$name-*" ":(glob,icase)**/${name}_*")
done
git ls-files -z -- "${names[@]}" ':(glob)**/LICENSES/**' \
  | while IFS= read -r -d '' path; do
    printf '%s\t%s\n' "$(sha256sum < "$path" | cut -c1-64)" "$path"
  done > "$scratch/files.tsv"

# The SPDX lines. The script builds the pattern from its parts, so this file
# holds no such line.
spdx="SPDX-License-""Identifier:"
git grep -I -n -o -E "$spdx[[:space:]]*[-A-Za-z0-9.+() /]+" -- . ":(exclude)$list" > "$scratch/spdx.txt" || true

jq -n -r \
  --rawfile files "$scratch/files.tsv" \
  --rawfile spdx "$scratch/spdx.txt" \
  --slurpfile allow "$scratch/allow.json" \
  --slurpfile list "$list" \
  --arg prefix "$spdx" \
  --arg owner "$owner" '
  def lines: split("\n") | map(select(length > 0));
  # A `path:line:match` line of git grep, split at its first two colons.
  def located: capture("^(?<path>[^:]*):(?<line>[0-9]+):(?<text>.*)$");
  # The licences of an SPDX expression: each id, with `A WITH B` as one.
  def ids:
    gsub("[()]"; " ") | [splits("[[:space:]]+") | select(length > 0)]
    | reduce .[] as $t ([]; if length >= 2 and .[-1] == "WITH" then .[:-2] + ["\(.[-2]) WITH \($t)"] else . + [$t] end)
    | map(select(IN("AND", "OR") | not));
  $list[0] as $list | $allow[0] as $allow
  | ($files | lines | map(split("\t") | {digest: .[0], path: .[1]})) as $files
  | [
      ($files[] | select($list.files[.digest] == null)
        | "check:licences: the licence file \(.path), of SHA-256 \(.digest), is outside the approved set; \($owner)"),
      ($spdx | lines[] | located
        | (.text | ltrimstr($prefix) | sub("[[:space:]]+$"; "")) as $expression
        | ($expression | ids | map(select(IN($allow[]) | not))) as $outside
        | select($outside | length > 0)
        | "check:licences: the SPDX line at \(.path):\(.line) brings \($outside | join(", ")), outside the allow list of deny.toml; \($owner)")
    ] as $refusals
  | if ($refusals | length) > 0 then ($refusals[], halt_error(1))
    else "check:licences: \($files | length) licence file(s) and \($spdx | lines | length) SPDX line(s) hold only approved licences"
    end'
