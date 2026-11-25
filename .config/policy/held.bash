#!/usr/bin/env bash
# Names the base of `allocation_free_region` and counts the functions that it
# holds for the change (#7632). `check:dylint` runs it after the policy run,
# whose evidence records are in `<records>`. The base records that
# `base-records.bash` writes are in `<base>`, and `held.jq` reads each unit.
# The count reads the product units alone: a test unit holds the functions of
# its library again, and the lint reads no test.
#
# Usage: held.bash <base> <records> <commit>
# `<commit>` is the base, and empty when no base stands.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
base=${1:?usage: held.bash <base> <records> <commit>}
records=${2:?usage: held.bash <base> <records> <commit>}
commit=${3-}
if [[ -z $commit ]]; then
  echo "held: no GATE_BASE names a base, so allocation_free_region holds the crates of its default alone"
  exit 0
fi
units=0
held=0
for record in "$base"/*.jsonl; do
  [[ -e $record ]] || continue
  name=${record##*/}
  [[ $name != *.test.jsonl && -e $records/$name ]] || continue
  reading=$(jq -n -c --rawfile base "$record" --rawfile head "$records/$name" -f "$here/held.jq")
  if [[ $(jq -r .read <<< "$reading") == true ]]; then
    units=$(( units + 1 ))
    held=$(( held + $(jq -r .held <<< "$reading") ))
  fi
done
echo "held: against the base ${commit:0:12}, allocation_free_region holds $held changed functions in $units units"
