#!/usr/bin/env bash
# `check:format`: the shared formatters of `treefmt.toml` over the paths that
# a change touches (#6883, `format.jq`). The gate of `pr:open` and the queue
# of `landing` read the change against `GATE_BASE`, a commit. The gate sets
# it to the fork from the trunk, and the queue sets it to the group's base.
# Without it, as in `gate:all`, the integration cycle and a run by hand, the
# check reads the whole tree.
#
# The change is every path that the working tree changes against the base
# and every untracked path that git does not ignore, as `select.bash` reads
# it. A deleted path is no file to format, but a link of a Markdown file can
# name it, so `format.jq` reads the deleted paths too. The gandr formatter
# stays out: `check:corpus-format` checks each gandr source with the driver
# that the Rust checks build, and here the driver would build from nothing.
# The type-aware lint of TypeScript reads the extension's packages, so the
# check installs them only when it formats a TypeScript source.
#
# Usage: format.bash
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
formatters=$(yq -p toml -o yaml '.formatter | keys | map(select(. != "gandr")) | join(",")' treefmt.toml)
if [[ -z ${GATE_BASE:-} ]]; then
  echo "format: no GATE_BASE names a base, so the check reads the whole tree" >&2
  mise run --quiet aube:install
  exec treefmt --ci --formatters "$formatters"
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# A shallow checkout, as the queue's, holds no commit but its head: the
# base's tree is fetched alone.
if ! git cat-file -e "$GATE_BASE^{commit}" 2> /dev/null; then
  git fetch --quiet --no-tags --depth=1 origin "$GATE_BASE"
fi
{
  git diff --no-renames --name-only --diff-filter=d "$GATE_BASE"
  git ls-files --others --exclude-standard
} > "$work/changed"
git diff --no-renames --name-only --diff-filter=D "$GATE_BASE" > "$work/deleted"
git ls-files > "$work/tracked"
# The paths reach jq as files, never as arguments: a large change makes a
# list longer than one argument can hold (#5220).
jq -n --rawfile changed "$work/changed" --rawfile deleted "$work/deleted" --rawfile tracked "$work/tracked" \
  '[$changed, $deleted, $tracked] | map(split("\n") | map(select(length > 0))) | {changed: .[0], deleted: .[1], tracked: .[2]}' \
  | jq -c -L "$here" -f "$here/format.jq" > "$work/paths"
if [[ $(< "$work/paths") == '"tree"' ]]; then
  # The paths that read as configuration or a pin, named for the log (#6976).
  jq -nr -L "$here" --rawfile changed "$work/changed" \
    'import "table" as $table; include "rows";
     $table::table[0].formatting.configuration as $rows
     | [$changed | split("\n")[] | select(length > 0) | . as $path | select(any($rows[]; mapped({path: .}; $path)))]
     | "format: the change touches \(length) paths of the formatter configuration or a pin, as \(.[:5] | join(" ")), so the check reads the whole tree"' >&2
  mise run --quiet aube:install
  exec treefmt --ci --formatters "$formatters"
fi
jq -r '.[]' "$work/paths" > "$work/list"
count=$(wc -l < "$work/list" | tr -d ' ')
if (( count == 0 )); then
  echo "format: the change against ${GATE_BASE:0:12} touches no path, so no formatter runs" >&2
  exit 0
fi
echo "format: $count paths that the change against ${GATE_BASE:0:12} touches" >&2
if grep -qE '\.m?ts$' "$work/list"; then mise run --quiet aube:install; fi
tr '\n' '\0' < "$work/list" | xargs -0 treefmt --ci --formatters "$formatters"
