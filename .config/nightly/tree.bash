#!/usr/bin/env bash
# Runs a command of the night in the night's tree, and gives that tree to the
# step as its output `tree` (#6868). `nightly.yml`'s `sweeps` runs its sweeps
# and its recovery sweep through it, and its uploads read the tree.
#
# On a hosted runner the tree is the job's checkout, and the command runs in
# it. On a runner of our own (`CI_RUNNER=integration`) the tree is one clone
# that the host keeps between nights, `~/.cache/gandr/night`. The clone keeps
# its target directory, so Cargo's fingerprints rebuild only what the night's
# commit changed, and no build state is restored. The clone has one path on
# its host. Each runner of a host has its own work directory, and Cargo's
# fingerprints hold the path of each source, so a clone in a work directory
# would build cold on each runner.
#
# The command runs in one gate slot of the host (`.config/mise/gated`), as a
# lane's gate runs. The clone's name gives the gate its lane, `night`. So two
# commands of the night take the lane's one lock in turn, and the night holds
# one slot at most beside the lanes' gates. Inside the slot the clone takes the
# checkout's commit: a fetch from the checkout, a forced checkout and a
# clean that keeps `target/`. A checkout writes only the files that the
# commit changed, so Cargo reads the other files as fresh. A crash in the
# middle leaves a partial target directory, and Cargo rebuilds what its
# fingerprints do not match. A new toolchain empties `target/`, since it
# rebuilds every unit, so a toolchain's stale units never grow the directory.
set -euo pipefail

# The half inside the slot, in the kept clone: `tree.bash --take <checkout>
# <command>...`.
if [[ ${1:-} == --take ]]; then
  checkout=$2
  shift 2
  git fetch --quiet --depth=1 --no-tags "$checkout" HEAD
  git checkout --quiet --force --detach FETCH_HEAD
  git clean --quiet -ffdx --exclude=/target
  toolchain=$(git hash-object rust-toolchain.toml)
  if [[ $(cat target/toolchain 2> /dev/null) != "$toolchain" ]]; then
    rm -rf target
    mkdir target
    printf '%s\n' "$toolchain" > target/toolchain
  fi
  exec "$@"
fi

if [[ ${CI_RUNNER:-} != integration ]]; then
  printf 'tree=%s\n' "$PWD" >> "${GITHUB_OUTPUT:-/dev/null}"
  exec "$@"
fi

tree=$HOME/.cache/gandr/night
checkout=$PWD
printf 'tree=%s\n' "$tree" >> "${GITHUB_OUTPUT:-/dev/null}"
mkdir -p "$tree"
git -C "$tree" init --quiet
cd "$tree"
# mise reads a configuration only under a trusted path. The host states its
# count of gate slots in its mise configuration, so the slot is taken under
# mise, as a lane's gate takes it.
export MISE_TRUSTED_CONFIG_PATHS=$tree
exec mise exec -- "$checkout/.config/mise/gated" "$checkout/.config/nightly/tree.bash" --take "$checkout" "$@"
