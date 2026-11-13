#!/usr/bin/env bash
# `check:jq-args` (#7091): a change adds no line where `--arg` or `--argjson`
# takes a shell expansion, unless the option and its name are an entry of
# `small.txt`. The kernel refuses one argument past 128 KiB, and a value of
# unbounded size then stops a landing or the cycle (#7062, #7076, #7089).
#
# The check runs the cases of `refuse.jq` first. It then reads the lines that
# the work adds against `GATE_BASE`, or against the merge base with the trunk.
# A workflow script is a shell, TOML or YAML file under `.config/` or
# `.github/`, `mise.toml`, or a file with no extension under them.
set -euo pipefail
here=$(dirname "${BASH_SOURCE[0]}")
.config/cases/run.bash jq-args "$here/cases.json" --program "$here/refuse.jq" --mode c
source .config/pr-stack/trunk.bash
base=${GATE_BASE:-$(git merge-base "origin/$trunk" HEAD)}
refusals=$(
  jq -n \
    --rawfile added <(
      git diff -U0 --no-color --no-ext-diff "$base" -- .config .github mise.toml \
        | awk '
          /^\+\+\+ / {
            file = substr($0, 7)
            name = file
            sub(/.*\//, "", name)
            script = file ~ /\.(bash|sh|toml|yml|yaml)$/ || name !~ /\./
            next
          }
          /^@@ / {
            split($3, at, ",")
            line = substr(at[1], 2) + 0
            next
          }
          /^\+/ {
            if (script) printf "%s\t%d\t%s\n", file, line, substr($0, 2)
            line++
          }'
    ) \
    --rawfile small "$here/small.txt" '
      {
        added: [$added | split("\n")[] | select(length > 0)
          | capture("^(?<file>[^\t]*)\t(?<line>[0-9]+)\t(?<text>.*)$")],
        small: [$small | split("\n")[] | select(length > 0 and (startswith("#") | not))]
      }' \
    | jq -c -f "$here/refuse.jq" \
    | jq -r '.[] | "check:jq-args: \(.)"'
)
if [[ -n $refusals ]]; then
  printf '%s\n' "$refusals" >&2
  exit 1
fi
echo "check:jq-args OK: the cases read as recorded, and no added line gives jq a shell value whose name is off the list"
