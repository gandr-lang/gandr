#!/usr/bin/env bash
# The `### Observed` block of a pull request's body (#3758), read off the
# change from a base to HEAD in the working directory's repository:
#
#   observed.bash <base> <body> <defect>
#
# <body> is the body's file and <defect> is `true` when the body works a
# `kind:defect` issue. The script gathers the transcripts the change adds
# under a crate's `tests/debug-traces/`, every path it touches and the
# `.config` cases it adds, and prints what `observed.jq` makes of them. Each
# input reaches jq through a file, never an argument, so a transcript of any
# size passes (#3871). The paths leave out a Rust file whose diff changes
# only comments (`comments.jq`, #5498): such a file has no test for lldb to
# stop in, as a change that touches no Rust has none.
set -euo pipefail
base=$1
body=$2
defect=$3
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
git diff --name-only --diff-filter=AM "$base" HEAD -- 'crates/*/tests/debug-traces/*.txt' \
  | while IFS= read -r path; do jq -Rs --arg path "$path" '{path: $path, text: .}' "$path"; done \
  | jq -s . > "$scratch/transcripts.json"
git diff -U0 --no-renames --no-color "$base" HEAD -- '*.rs' | jq -Rs -f "$here/comments.jq" > "$scratch/comments.json"
git diff --name-only "$base" HEAD | jq -R . | jq -s --slurpfile comments "$scratch/comments.json" '. - $comments[0]' > "$scratch/paths.json"
# A change touching no Rust is witnessed by a `.config` case it adds (#3784):
# every name a JSON file under `.config` holds at HEAD and did not hold at the
# base, and every `fail "#<n>: …"` line a `cases.bash` under `.config` adds,
# its quoted text the name (#4863).
{
  git diff --name-only --diff-filter=AM "$base" HEAD -- ':(glob).config/**/*.json' \
    | while IFS= read -r path; do
        git show "$base:$path" 2> /dev/null | jq -c '[.. | objects | .name? | strings]' > "$scratch/before.json" 2> /dev/null \
          || echo '[]' > "$scratch/before.json"
        [[ -s $scratch/before.json ]] || echo '[]' > "$scratch/before.json"
        jq -c --arg path "$path" --slurpfile before "$scratch/before.json" \
          '[.. | objects | .name? | strings] - $before[0] | map({path: $path, name: .})' "$path"
      done
  git diff -U0 --no-renames --no-color "$base" HEAD -- ':(glob).config/**/*cases.bash' \
    | jq -Rs '[foreach (split("\n")[]) as $line ({path: null};
        if ($line | startswith("+++ ")) then {path: ($line | sub("^\\+\\+\\+ (b/)?"; ""))}
        else {path, text: (if ($line | startswith("+")) then $line[1:] else null end)} end;
        select(.text != null) | {path, name: (.text | capture("\\bfail\\s+\"(?<name>#[0-9]+:[^\"]*)\"").name)})]'
} | jq -s 'add // []' > "$scratch/cases.json"
jq -n --argjson defect "$defect" --rawfile body "$body" \
  --slurpfile transcripts "$scratch/transcripts.json" \
  --slurpfile paths "$scratch/paths.json" \
  --slurpfile cases "$scratch/cases.json" \
  '{defect: $defect, body: $body, transcripts: $transcripts[0], paths: $paths[0], cases: $cases[0]}' \
  | jq -r -f "$here/observed.jq"
