#!/usr/bin/env bash
# `ledger:stamp <pr> <base>` writes the number of a pull request into the
# features ledger rows that its change touches. `pr:land` refuses a named row
# when its `since` lacks `#<pr>`. GitHub gives the number only when `pr:open`
# creates the pull request. So the script writes the number after the
# opening.
# - see: #7978, `.config/bodies/ledger.jq`
#
# A row to stamp is one that the change from `<base>` to `HEAD` adds or
# edits. It has the status `implemented` or `partial`, and its `since` lacks
# `#<pr>`. `since` is the last value of the row's `INSERT` line. A `NULL`
# becomes `'#<pr>'`, and a text gets ` #<pr>` at its end. No other byte
# changes.
#
# The script reads the stamped file back through `sqlite3`. Each row must keep
# every other value, and only the stamped rows change their `since`. Else
# the stamp is refused. Then the script commits the ledger file alone. A row
# that carries the number stays as it is, so a second run commits nothing.
#
# Exits 0 when it commits or has nothing to write, 2 on a refusal.
set -euo pipefail
pr=${1:?usage: stamp.bash <pr> <base>}
base=${2:?usage: stamp.bash <pr> <base>}
file=ledger/features.sql
[[ $pr =~ ^[0-9]+$ ]] || { echo "ledger:stamp: the pull request is a number, not \`$pr\`" >&2; exit 2; }
git rev-parse --verify --quiet "$base^{commit}" > /dev/null || { echo "ledger:stamp: the base \`$base\` names no commit" >&2; exit 2; }
git diff --quiet HEAD -- "$file" || { echo "ledger:stamp: $file holds changes that no commit holds; commit them, then run the task again" >&2; exit 2; }
tables=$(mktemp -d)
trap 'rm -rf "$tables"' EXIT
rows() { { cat; printf '%s\n' 'SELECT * FROM feature ORDER BY id;'; } | sqlite3 -json; }
{ git show "$base:$file" 2> /dev/null || true; } | rows > "$tables/base.json"
git show "HEAD:$file" | rows > "$tables/head.json"
jq -nr --argjson pr "$pr" --slurpfile base "$tables/base.json" --slurpfile head "$tables/head.json" '
  ($base | add // []) as $base | ($head | add // []) as $head
  | (INDEX($base[]; .id)) as $was
  | $head[]
  | select($was[.id] != .)
  | select(.status | IN("implemented", "partial"))
  | select((.since // "") | test("#\($pr)\\b") | not)
  | .id' > "$tables/ids"
if [[ ! -s $tables/ids ]]; then
  echo "ledger:stamp: no row that the change touches lacks #$pr"
  exit 0
fi
awk -v pr="$pr" -v q="'" -v ids="$tables/ids" '
  BEGIN { while ((getline id < ids) > 0) want[id] = 1 }
  {
    head = "INSERT INTO feature VALUES(" q
    if (index($0, head) == 1) {
      rest = substr($0, length(head) + 1)
      id = substr(rest, 1, index(rest, q) - 1)
      if (id in want) {
        if ($0 ~ /,NULL\);$/) sub(/,NULL\);$/, "," q "#" pr q ");")
        else if (substr($0, length($0) - 2) == q ");") $0 = substr($0, 1, length($0) - 3) " #" pr q ");"
        else { printf "ledger:stamp: the line of `%s` does not end in its since value\n", id > "/dev/stderr"; bad = 1 }
        done[id] = 1
      }
    }
    print
  }
  END {
    for (id in want) if (!(id in done)) { printf "ledger:stamp: no line holds the row `%s`\n", id > "/dev/stderr"; bad = 1 }
    exit bad
  }' "$file" > "$tables/stamped.sql" || exit 2
rows < "$tables/stamped.sql" > "$tables/stamped.json"
if ! jq -ne --argjson pr "$pr" --slurpfile head "$tables/head.json" --slurpfile now "$tables/stamped.json" \
  --rawfile ids "$tables/ids" '
  ($head | add // []) as $head | ($now | add // []) as $now
  | (INDEX($now[]; .id)) as $by
  | ($ids | split("\n") | map(select(. != ""))) as $ids
  | ($head | length) == ($now | length)
    and all($head[]; . as $row | $by[$row.id] as $new
      | $new != null
        and ($row | del(.since)) == ($new | del(.since))
        and $new.since == (if ($ids | index($row.id)) == null then $row.since
          elif $row.since == null then "#\($pr)"
          else "\($row.since) #\($pr)" end))' > /dev/null; then
  echo "ledger:stamp: the stamped $file changes more than the since of the rows it stamps; it is refused" >&2
  exit 2
fi
count=$(wc -l < "$tables/ids")
read -r added removed _ < <(git diff --no-index --numstat -- "$file" "$tables/stamped.sql" || true)
if [[ $added != "$count" || $removed != "$count" ]]; then
  echo "ledger:stamp: the stamped $file changes $added line(s) for $count row(s); it is refused" >&2
  exit 2
fi
cp "$tables/stamped.sql" "$file"
git add -- "$file"
# The file held no change before the stamp, so a failed commit gives it back
# as `HEAD` holds it, and a second run starts clean.
if ! git commit --quiet -m "chore(repo): the ledger rows of #$pr carry its number" \
  -m "pr:land refuses a named row whose since lacks the number of the
pull request. The stamp writes #$pr into each implemented or
partial row that the change touches." \
  -m "Co-authored-by: silvanshade <silvanshade@users.noreply.github.com>
Assisted-by: LLM" -- "$file"; then
  git restore --staged --worktree -- "$file"
  echo "ledger:stamp: the commit of the stamp failed, and $file is as HEAD holds it" >&2
  exit 2
fi
echo "ledger:stamp: #$pr is in the since of $(paste -sd ' ' "$tables/ids")"
