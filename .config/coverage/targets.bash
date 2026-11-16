#!/usr/bin/env bash
# The integration targets of the tree, as `targets.jq` reads them (#7195):
# each `[[test]]` table of `crates/*/Cargo.toml`, and each `tests/*.rs` of a
# crate that discovers its targets. Prints one refusal a line for each target
# whose file holds no item, and exits 1 when it prints one.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
targets() {
  local manifest crate path name
  for manifest in crates/*/Cargo.toml; do
    crate=${manifest%/Cargo.toml}
    while IFS=$'\t' read -r name path; do
      [[ -n $name ]] || continue
      jq -nc --arg file "$manifest" --arg name "$name" --arg path "$path" --rawfile code "$crate/$path" \
        '{file: $file, name: $name, path: $path, code: $code}'
    done < <(yq -p toml -o tsv '.test // [] | .[] | [.name, .path // ("tests/" + .name + ".rs")]' "$manifest")
    # yq's `//` takes `false` as absent, so the value is read as it stands.
    if [[ $(yq -p toml -o json '.package.autotests' "$manifest") != false ]]; then
      for path in "$crate"/tests/*.rs; do
        [[ -e $path ]] || continue
        name=${path##*/}
        jq -nc --arg file "$manifest" --arg name "${name%.rs}" --arg path "${path#"$crate"/}" --rawfile code "$path" \
          '{file: $file, name: $name, path: $path, code: $code}'
      done
    fi
  done
}
refusals=$(targets | jq -s -r -f "$here/targets.jq" | jq -r '.[]')
if [[ -n $refusals ]]; then
  printf '%s\n' "$refusals" >&2
  exit 1
fi
