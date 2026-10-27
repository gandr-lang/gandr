#!/usr/bin/env bash
# The one runner for the jq-over-cases checks (#3039). A cases file is a JSON
# array; each case holds a `name`, an `input`, and either the `output` the
# program gives for it or `"fails": true` when the program must refuse it. A
# case may hold `args`, each passed as `--argjson`, and, under `--programs`,
# the `program` it runs. The program reads the input on standard input and
# includes modules from its own directory and each `-L`. An `output` string is
# compared as the text the program prints; any other output as its compact
# JSON.
#
# Usage: run.bash <kind> <cases> (--program <file> | --programs <dir>)
#   [--mode r|c|j] [--raw <program>]... [-L <dir>]...
# `--mode` prints raw text (`r`, the default), compact JSON (`c`), or compact
# JSON and raw text without a newline (`j`); `--raw` prints the named program
# of a `--programs` file as raw text. Prints each failing case under its kind
# and program, and exits 1 on any; 2 on a malformed invocation.
set -euo pipefail
usage() {
  echo 'usage: run.bash <kind> <cases> (--program <file> | --programs <dir>) [--mode r|c|j] [--raw <program>]... [-L <dir>]...' >&2
  exit 2
}
(( $# >= 2 )) || usage
kind=$1
file=$2
shift 2
program=
programs=
mode=r
raw=()
libs=()
while (( $# )); do
  (( $# >= 2 )) || usage
  case $1 in
    --program) program=$2 ;;
    --programs) programs=$2 ;;
    --mode) mode=$2 ;;
    --raw) raw+=("$2") ;;
    -L) libs+=(-L "$2") ;;
    *) usage ;;
  esac
  shift 2
done
[[ -n $program || -n $programs ]] || usage
err=$(mktemp)
trap 'rm -f "$err"' EXIT
failed=0
while IFS= read -r case; do
  name=$(jq -r .name <<< "$case")
  path=${program:-$programs/$(jq -r .program <<< "$case")}
  reading=$mode
  for named in "${raw[@]}"; do
    if [[ ${path##*/} == "$named" ]]; then reading=r; fi
  done
  case $reading in
    r) flags=(-r) ;;
    c) flags=(-c) ;;
    j) flags=(-j -c) ;;
    *) usage ;;
  esac
  mapfile -t args < <(jq -r '(.args // {}) | to_entries[] | "--argjson", .key, (.value | tojson)' <<< "$case")
  fails=$(jq '.fails // false' <<< "$case")
  label="$kind case FAILED (${path##*/}): $name"
  if got=$(jq .input <<< "$case" | jq "${flags[@]}" -L "$(dirname "$path")" "${libs[@]}" "${args[@]}" -f "$path" 2> "$err"); then
    if [[ $fails == true ]]; then
      printf '%s\n  gave:\n%s\n  wanted: a refusal\n' "$label" "$got" >&2
      failed=1
    else
      want=$(jq -r 'if (.output | type) == "string" then .output else (.output | tojson) end' <<< "$case")
      if [[ "$got" != "$want" ]]; then
        printf '%s\n  gave:\n%s\n  wanted:\n%s\n' "$label" "$got" "$want" >&2
        failed=1
      fi
    fi
  elif [[ $fails != true ]]; then
    printf '%s\n  refused:\n%s\n' "$label" "$(< "$err")" >&2
    failed=1
  fi
done < <(jq -c '.[]' "$file")
exit "$failed"
