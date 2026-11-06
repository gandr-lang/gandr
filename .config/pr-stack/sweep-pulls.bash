#!/usr/bin/env bash
# `wt:sweep` asks about the merged pull requests of its branches in one call
# at most, and asks about a branch at a head only once (#5839), run by
# `check:pr-stack` over the cases in `pulls.json`. Each case calls
# `merged_pulls` on a fresh record directory, `runs` times in a row. A stub
# `gh` answers as GitHub would, through the filter that `--jq` gives it:
# - each alias `b<i>` holds the merged pull request of `merged` for its
#   branch, or none;
# - a `-F` variable that holds a number or a boolean fails the query, as
#   GitHub refuses an Int where the query asks for a `String!`;
# - with `fail`, every call fails.
# A case names its branches, or a `count` of `branch-<k>`, the branches
# `recorded` before the first run with one pull request `#1`, and the `head`
# of each branch, `c1` unless it names another. Its `output` is one line:
# the calls of each run, the aliases of each call, the record files by name,
# or their count above 5 branches, and the answers of the last run. A case
# with `facts` puts its fact lines and its `answers` through
# `pulls_into_facts` instead. Its `output` gives the count of lines out and
# the `pulls` of each, by branch, `-` for a line with no branch.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/sweep.bash"
cases=$here/pulls.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-sweep-pulls.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

gh() {
  local filter= value
  local -a pairs=()
  printf 'call\n' >> "$work/calls"
  while (( $# > 0 )); do
    case $1 in
      -f | -F)
        if [[ $2 == h[0-9]*=* ]]; then
          value=${2#*=}
          if [[ $1 == -F && ( $value =~ ^[0-9]+$ || $value == true || $value == false ) ]]; then return 1; fi
          pairs+=("${2%%=*}" "$value")
        fi
        shift 2
        ;;
      --jq) filter=$2; shift 2 ;;
      *) shift ;;
    esac
  done
  echo $(( ${#pairs[@]} / 2 )) >> "$work/aliases"
  [[ $fail == false ]] || return 1
  jq -n --argjson merged "$merged" --args \
    '$ARGS.positional as $p | [range(0; $p | length; 2) | [$p[.], $p[. + 1]] | {key: ("b" + (.[0] | ltrimstr("h"))), value: {nodes: (
      if $merged[.[1]] then [{number: $merged[.[1]], commits: {nodes: [{commit: {messageHeadline: (.[1] + " own")}}]}}] else [] end)}}]
      | from_entries | {data: {repository: .}}' "${pairs[@]}" \
    | jq -r "$filter"
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  if [[ $(jq -r ".[$i] | has(\"facts\")" "$cases") == true ]]; then
    actual=$(jq -c ".[$i].facts[]" "$cases" | pulls_into_facts "$(jq -c ".[$i].answers" "$cases")" \
      | jq -rs '"facts \(length); pulls " + (map("\(.branch // "-")=\(if .pulls == null then "null" else "#\(.pulls[0].number)" end)") | join(" "))')
    if [[ $actual != "$expected" ]]; then
      printf 'wt:sweep pulls case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
      failed=1
    fi
    continue
  fi
  merged=$(jq -c ".[$i].merged" "$cases")
  fail=$(jq -r ".[$i].fail // false" "$cases")
  runs=$(jq -r ".[$i].runs" "$cases")
  head=$(jq -r ".[$i].head // \"c1\"" "$cases")
  mapfile -t branches < <(jq -r ".[$i] | if .count then range(1; .count + 1) | \"branch-\\(.)\" else .branches[] end" "$cases")
  dir=$work/$i
  mkdir -p "$dir"
  while IFS= read -r branch; do
    [[ -n $branch ]] || continue
    file=${branch//%/%25}
    mkdir -p "$dir/c1"
    echo '[{"number":1,"subjects":["kept"]}]' > "$dir/c1/${file//\//%2F}.json"
  done < <(jq -r ".[$i].recorded // [] | .[]" "$cases")
  args=()
  for branch in "${branches[@]}"; do args+=("$branch" "$head"); done
  calls=()
  : > "$work/aliases"
  for (( run = 0; run < runs; run++ )); do
    : > "$work/calls"
    answers=$(merged_pulls "$dir" "${args[@]}")
    calls+=("$(wc -l < "$work/calls" | tr -d ' ')")
  done
  aliases=$(paste -sd ' ' "$work/aliases")
  mapfile -t records < <(find "$dir" -name '*.json' | sed 's|.*/||; s|\.json$||' | LC_ALL=C sort)
  if (( ${#branches[@]} > 5 )); then
    listed=${#records[@]}
    told="${#branches[@]}, $(jq -r 'to_entries | map(select(.value | length > 0) | "\(.key)=#\(.value[0].number)") | join(" ")' <<< "$answers")"
  else
    listed=${records[*]:-none}
    told=$(jq -r --args '. as $a | $ARGS.positional | map(. as $b | $a[$b] | "\($b)=\(if . == null then "null" elif length == 0 then "-" else "#\(.[0].number)" end)") | join(" ")' "${branches[@]}" <<< "$answers")
  fi
  actual="calls $(IFS=,; echo "${calls[*]}" | sed 's/,/, /g'); aliases ${aliases:-none}; records $listed; answers $told"
  if [[ $actual != "$expected" ]]; then
    printf 'wt:sweep pulls case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "wt:sweep pulls OK: $count cases ask about each branch at a head once, in one call at most"
