#!/usr/bin/env bash
# Run each case of cases.txt on the native driver and on the wasm32-wasip3
# driver under Wasmtime, and compare what each prints and whether each
# succeeded. WASI 0.3 states only success or failure on exit, so an exit
# code is compared as that alone. Both drivers start in `/` with an empty
# store and configuration of their own, so a path prints alike on both.
# Wasmtime preopens the host's root at `/`: `std::fs::canonicalize` resolves
# an absolute path only through a root preopen. The native driver runs with
# `GANDR_TOOLCHAIN_HANDOFF=never`, so it is the build named and never the
# default toolchain (#7440). The first line gives what it does under the
# caller's own environment: the line that names its hand-off, or `none`.
#
# Usage: compare.bash <native gandr> <gandr.wasm>
set -euo pipefail

native=$(realpath "$1")
module=$(realpath "$2")
root=$(pwd -P)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/native/data" "$scratch/native/config" "$scratch/wasm/data" "$scratch/wasm/config"

handoff=$(env -u GANDR_TOOLCHAIN_HANDOFF "$native" --version 2>&1 > /dev/null \
  | awk '/^gandr: .* hands off to / { print; exit }') || true
echo "native: $native, hand-off: ${handoff:-none}"

on_native() {
  (cd / && env -i PATH="$PATH" GANDR_TOOLCHAIN_HANDOFF=never XDG_DATA_HOME="$scratch/native/data" XDG_CONFIG_HOME="$scratch/native/config" "$native" "$@")
}

on_wasm() {
  wasmtime run -W tail-call=y -S p3=y --dir /::/ \
    --env XDG_DATA_HOME="$scratch/wasm/data" --env XDG_CONFIG_HOME="$scratch/wasm/config" \
    "$module" "$@"
}

differed=0
while read -r verb path; do
  [[ -z $verb || $verb == '#'* ]] && continue
  native_status=0
  native_output=$(on_native "$verb" "$root/$path" < /dev/null 2>&1) || native_status=1
  wasm_status=0
  wasm_output=$(on_wasm "$verb" "$root/$path" < /dev/null 2>&1) || wasm_status=1
  if [[ $native_output == "$wasm_output" && $native_status == "$wasm_status" ]]; then
    echo "agrees: $verb $path"
  else
    echo "differs: $verb $path (native $native_status, wasm $wasm_status)"
    diff <(printf '%s\n' "$native_output") <(printf '%s\n' "$wasm_output") || true
    differed=1
  fi
done < .config/wasm/cases.txt
exit "$differed"
