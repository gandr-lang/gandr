# shellcheck shell=bash
# The environment of a tree (#7485, #7486), sourced by each tool that runs
# the commands of a tree other than the caller's: the replay's checks
# (`replay/stale.bash`), the records of `check:deletes`
# (`deletes/records.bash`) and the builds of the toolchain follower
# (`follow/follow.bash`). mise sets `RUSTUP_TOOLCHAIN` and the paths of the
# tools from the tree where it starts, and the variable overrides
# `rust-toolchain.toml`. So the caller's environment carries the pin of the
# caller's tree, and a command in another tree builds under that pin unless
# it gets the environment of its own tree.

# The channel that the tree in the directory `$1` pins in its
# `rust-toolchain.toml`, or nothing.
tree_channel() {
  [[ -f $1/rust-toolchain.toml ]] || return 0
  sed -n 's/^channel = "\([^"]*\)".*/\1/p' "$1/rust-toolchain.toml"
}

# Runs `$2...` in the directory `$1`, in the environment of that tree: the
# variables and the paths of the tools that mise gives the tree, and the
# channel that the tree pins as `RUSTUP_TOOLCHAIN`. The command runs in a
# subshell, so a shell function runs as a program does, and the caller's
# environment stays as it is. mise trusts the tree and installs nothing: a
# tool that the tree pins and the host lacks fails the command. A tree that
# pins no channel is refused by name with status 2, and the command does not
# run.
tree_exec() {
  local dir channel
  dir=$(cd "$1" && pwd -P) || return 2
  shift
  channel=$(tree_channel "$dir")
  if [[ -z $channel ]]; then
    echo "error: $dir pins no toolchain in rust-toolchain.toml, so \`$1\` does not run under the caller's" >&2
    return 2
  fi
  (
    cd "$dir" || exit 2
    export MISE_TRUSTED_CONFIG_PATHS=$dir${MISE_TRUSTED_CONFIG_PATHS:+:$MISE_TRUSTED_CONFIG_PATHS}
    environment=$(mise env --shell bash) || { echo "error: mise gives no environment for $dir" >&2; exit 2; }
    eval "$environment"
    export RUSTUP_TOOLCHAIN=$channel
    "$@"
  )
}
