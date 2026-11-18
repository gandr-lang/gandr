#!/usr/bin/env bash
# The shared runner executes jq checks over cases (#3039). A cases file is a
# JSON array. Each case has a `name` and an `input`. It has an `output` or
# `"fails": true`. The runner expects refusal when `fails` is true. A case may
# have `args`. The runner passes each arg as `--argjson`. A case under
# `--programs` has a `program`. The program reads input on standard input.
# The runner includes its directory and each `-L` directory. It compares string
# output as printed text. It compares another output as compact JSON.
#
# Usage: run.bash <kind> <cases> (--program <file> | --programs <dir>)
#   [--mode r|c|j] [--raw <program>]... [-L <dir>]...
# `--mode` prints raw text in `r` mode. It prints compact JSON in `c` mode.
# It prints compact JSON and raw text with no newline in `j` mode. `--raw`
# prints its named program in a `--programs` directory as raw text. It prints
# each failing case under its kind and program. It exits 1 on any failure. It
# exits 2 on a malformed invocation or a cases file that is not a JSON array.
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
if ! jq -e 'type == "array"' "$file" > /dev/null; then
  printf 'runner refuses cases file that is not a JSON array: %s\n' "$file" >&2
  exit 2
fi
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
