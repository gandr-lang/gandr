#!/usr/bin/env bash
# Writes the base records that `allocation_free_region` reads in
# `check:dylint` (#7419) to `<out>`: the evidence records, at the base, of
# each package that the change touches. The lint then holds to the default
# each function of such a package whose body differs from its record, or
# that its record lacks. A package that the change does not touch has no
# record, and the lint holds none of its functions. A record of another hash
# scheme, from an earlier library or another toolchain, holds nothing too.
#
# The records come from `.config/deletes/records.bash`, as the base side of
# `check:deletes` takes them, so the two checks share one cache (#6823). A
# package that the change adds has no manifest at the base. Each of its
# library, binary and proc-macro units takes an empty record, and the lint
# holds each of its functions. Its test units take no record, since the
# default leaves a test out.
#
# The change runs from `<base>` to the working state, with each edit and
# each new file that no commit holds yet. A package is touched when a path
# that the change touches is inside its directory.
#
# Usage: base-records.bash <base> <out>
# `<out>` is a directory that holds nothing. Exits 2 when the records do not
# build. A clone that does not hold the base fetches it alone, as the job of a
# merge group checks out its own commit at a depth of one (#7632).
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git rev-parse --show-toplevel)
if ! git cat-file -e "${1:?usage: base-records.bash <base> <out>}^{commit}" 2> /dev/null; then
  git fetch --quiet --no-tags --depth=1 origin "$1" || :
fi
base=$(git rev-parse --verify --quiet "$1^{commit}") \
  || { echo "base-records: $1 is no commit" >&2; exit 2; }
out=$(cd "${2:?usage: base-records.bash <base> <out>}" && pwd)
scratch=$(mktemp -d)
cleanup() {
  if [[ -d $scratch/base ]]; then git -C "$root" worktree remove --force "$scratch/base" > /dev/null 2>&1 || :; fi
  rm -rf "$scratch"
}
trap cleanup EXIT
{
  git -C "$root" diff --no-renames --name-only "$base" -- crates/
  git -C "$root" ls-files --others --exclude-standard -- crates/
} > "$scratch/changed"
[[ -s $scratch/changed ]] || exit 0
# Each touched package: its name, its directory, and the record name of each
# product unit, as `evidence::record_name` forms it from the root file that
# Cargo passes, relative to the workspace.
touched=$(cargo metadata --format-version 1 --no-deps --locked --manifest-path "$root/Cargo.toml" \
  | jq -c --arg root "$root/" --rawfile changed "$scratch/changed" '($changed | split("\n") | map(select(. != ""))) as $changed
    | [.packages[]
    | {name, dir: (.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml"))}
      + {products: [.targets[] | select(.kind[0] | IN("lib", "rlib", "dylib", "cdylib", "staticlib", "proc-macro", "bin"))
        | (.src_path | ltrimstr($root) | gsub("[^A-Za-z0-9_-]"; "_")) + "."
          + (.crate_types[0] | if . == "lib" or . == "rlib" then "lib" else . end) + ".jsonl"]}
    | select(.dir as $dir | $changed | any(startswith($dir + "/")))]')
args=()
while IFS=$'\t' read -r name dir products; do
  if git -C "$root" cat-file -e "$base:$dir/Cargo.toml" 2> /dev/null; then
    args+=("$name=$dir")
  else
    for product in $products; do : > "$out/$product"; done
  fi
done < <(jq -r '.[] | [.name, .dir, (.products | join(" "))] | @tsv' <<< "$touched")
(( ${#args[@]} )) || exit 0
git -C "$root" worktree add --quiet --detach "$scratch/base" "$base"
# The base builds as the policy run of `check:dylint` builds the head: its
# features unify over the workspace, and the scope's required features stand
# on, each with the package that owns it (#7654). Built per package with its
# own features alone, a record lacks each function behind a feature that the
# policy run turns on, and the lint holds each such function as new. The
# base's own `required.bash` reads the scope, so a feature that the base
# lacks is not asked.
policy_features=
if [[ -x $scratch/base/.config/policy/required.bash ]]; then
  # shellcheck disable=SC2086 # `GATE_SCOPE` is a list of arguments.
  policy_features=$(cargo metadata --no-deps --locked --format-version 1 --manifest-path "$scratch/base/Cargo.toml" \
    | "$scratch/base/.config/policy/required.bash" ${GATE_SCOPE:---workspace})
fi
summary=$(RECORDS_POLICY=1 RECORDS_POLICY_FEATURES=${policy_features#--features } \
  "$here/../deletes/records.bash" "$scratch/base" "$root/target/deletes" "$out" "${args[@]}") || exit 2
echo "base-records: ${#args[@]} touched packages at ${base:0:12}; ${summary#*: }" >&2
