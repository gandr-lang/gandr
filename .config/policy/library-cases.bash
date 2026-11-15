#!/usr/bin/env bash
# A policy run writes nothing into the checkouts of the cargo home (#7492).
# `check:dylint` runs the case after its own run, through its own command
# (`policy`). The case gives the run a cargo home of its own, with no
# network. That home holds one checkouts directory under each name of
# quenchant's checkouts in the cargo home of the gate. Each directory holds
# one empty checkout. A scratch workspace carries the library entry of this
# workspace's metadata. A run that resolves that entry writes a dummy crate
# into each empty checkout, and the checkout then has a new time. The case
# reads only those times, so the exit of the run tells it nothing.
# Dylint reads the metadata of the working directory, so the run starts in
# the scratch workspace. That workspace stands under `target`, so the run
# takes the lane of this tree, and `.config` there points at this tree's.
set -euo pipefail
declare -F policy > /dev/null || { echo "library case: run it from check:dylint, which exports \`policy\`" >&2; exit 2; }
mkdir -p target
scratch=$(mktemp -d "$PWD/target/library-case.XXXXXX")
trap 'rm -rf "$scratch"' EXIT

shopt -s nullglob
names=("${CARGO_HOME:-$HOME/.cargo}"/git/checkouts/quenchant-*)
shopt -u nullglob
if (( ${#names[@]} == 0 )); then
  echo "library case FAILED: the cargo home holds no checkout of quenchant, so the case has no name to give its checkouts"
  exit 1
fi
home=$scratch/cargo-home
checkouts=()
for name in "${names[@]}"; do
  mkdir -p "$home/git/checkouts/${name##*/}/case"
  checkouts+=("$home/git/checkouts/${name##*/}/case")
done
times() { stat -c '%n %y' "${checkouts[@]}"; }
before=$(times)

libraries=$(cargo metadata --no-deps --format-version 1 --locked | jq -r '
  .metadata.dylint.libraries[]
  | "[[workspace.metadata.dylint.libraries]]\ngit = \(.git | tojson)\nrev = \(.rev | tojson)\npattern = \(.pattern | tojson)\n"')
mkdir -p "$scratch/workspace/src"
printf '[package]\nname = "library-case"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n\n[workspace]\n\n%s' \
  "$libraries" > "$scratch/workspace/Cargo.toml"
: > "$scratch/workspace/src/lib.rs"
ln -s "$PWD/.config" "$scratch/workspace/.config"
cp rust-toolchain.toml "$scratch/workspace/"
(
  cd "$scratch/workspace"
  CARGO_HOME=$home CARGO_NET_OFFLINE=true CARGO_TERM_COLOR=never policy --package library-case > "$scratch/run.txt" 2>&1
) || true

after=$(times)
if [[ $after != "$before" ]]; then
  echo "library case FAILED: #7492: the policy run writes into the checkouts of its cargo home"
  echo "  got: $(diff <(echo "$before") <(echo "$after") | grep -c '^>') of ${#checkouts[@]} checkouts with a new time"
  exit 1
fi
echo "library case OK: the policy run writes nothing into the ${#checkouts[@]} checkouts of its cargo home"
