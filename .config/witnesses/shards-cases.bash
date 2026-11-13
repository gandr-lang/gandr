#!/usr/bin/env bash
# Each enforcing shard lists every package whose tests its members' witnesses
# name (#7089), run by `check:witness-cases`. A witness spelled
# `<package>::<path>` names a test of another package (#7039), and a shard
# resolves its members' witnesses against its own listing. So the package
# that a witness names stands in its owner's shard. The shards are the
# matrix of `cargo-test-enforcing-shard` in `ci.yml`: each shard's
# `packages`, and the shard of `excludes`, `rest`, that takes every other
# package. On 962d3729c the split of #6885 left `gandr-surface-lowering-base`
# in `rest`, while two witnesses of `gandr-surface-lowering` in `lowering`
# named its tests, and the integration cycle failed.
#
# The cases read the tree's witnesses and its packages. The tree's `ci.yml`
# gives no refusal. A copy whose `lowering` shard leaves the base crate out
# gives the refusal that names it.
set -euo pipefail
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
fail() {
  echo "witness-shards: $*" >&2
  failed=1
}

# Each workspace package and its directory below the tree, longest first, so
# a nested package takes its own files.
cargo metadata --locked --no-deps --format-version 1 \
  | jq -r --arg root "$PWD/" '[.packages[] | {name, dir: (.manifest_path | ltrimstr($root) | sub("/?Cargo.toml$"; ""))}]
      | sort_by(.dir | length) | reverse[] | "\(.dir)\t\(.name)"' > "$scratch/packages"
# Each witness that names another package's test: its file and the package.
git grep -n -o -E 'witness: `gandr-[a-z0-9-]+::' -- 'crates/*.rs' \
  | awk -F: '{ named = $0; sub(/.*witness: `/, "", named); sub(/::$/, "", named); print $1 "\t" named }' > "$scratch/witnesses"

# The refusals of the shards of `$1`: one line for each owner and named
# package in two shards.
refusals() {
  yq -o json 'explode(.) | .jobs["cargo-test-enforcing-shard"].strategy.matrix.include' "$1" \
    | jq -r '.[] | select(.packages != null) | .shard as $shard | .packages | split(" ")[] | select(. != "") | "\(.)\t\($shard)"' \
    > "$scratch/shards"
  awk -F'\t' '
    FILENAME == ARGV[1] { dirs[++n] = $1; names[n] = $2; next }
    FILENAME == ARGV[2] { shard[$1] = $2; next }
    {
      owner = ""
      for (i = 1; i <= n; i++) if (index($1, dirs[i] "/") == 1) { owner = names[i]; break }
      if (owner == "" || owner == $2) next
      a = (owner in shard) ? shard[owner] : "rest"
      b = ($2 in shard) ? shard[$2] : "rest"
      if (a != b) print owner " in " a " names a test of " $2 " in " b " (" $1 ")"
    }
  ' "$scratch/packages" "$scratch/shards" "$scratch/witnesses" | sort -u
}

got=$(refusals .github/workflows/ci.yml)
[[ -z $got ]] || fail "#7089: a shard of ci.yml leaves out a package whose tests its members' witnesses name: $got"

awk '{ sub(/ gandr-surface-lowering-base$/, ""); print }' .github/workflows/ci.yml > "$scratch/ci.yml"
got=$(refusals "$scratch/ci.yml")
[[ $got == *"gandr-surface-lowering in lowering names a test of gandr-surface-lowering-base in rest"* ]] \
  || fail "#7089: a lowering shard without gandr-surface-lowering-base gave no refusal: ${got:-none}"

(( failed == 0 )) || exit 1
echo "witness shards OK: each shard lists the packages whose tests its members' witnesses name, and a shard that leaves one out is refused"
