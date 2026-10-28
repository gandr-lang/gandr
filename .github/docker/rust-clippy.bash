#!/usr/bin/env bash
# Runs a command that builds a Dylint driver against a pinned rust-clippy:
#   rust-clippy.bash <repository> <channel> <command>…
# dylint_driver's build script clones rust-clippy, checks out the ref
# `master` and walks first parents back to the commit that set the
# toolchain's channel; it reads no pin of ours, and rust-clippy's default
# branch is `main`. The clone is served from <repository>, a local repository
# holding the pinned commit as `master`, through a rewrite scoped to the one
# command. The repository is fetched once, at depth 2, and kept: the walk
# stops at the commit's first parent, whose channel differs. The CI image's
# driver stage and `check:dylint` both run through here.
#
# The pin is the commit under rust-clippy's rust-<stable> tag that set the
# channel, the tag quenchant's clippy_utils pins; `mise run toolchain:bump`
# moves it with the channel. A commit naming another channel than <channel>,
# or whose parent names the same, is refused. `RUST_CLIPPY_URL` names another
# source to fetch the commit from.
set -euo pipefail
# rust-clippy's rust-1.98.0, the commit that set nightly-2026-06-25.
rev=64c7431d6cd823d1a7663165c7e59d78e6dc726a
(( $# > 2 )) || { echo 'usage: rust-clippy.bash <repository> <channel> <command>…' >&2; exit 2; }
repository=$1 channel=$2
shift 2

# A complete repository is renamed into place, so an interrupted fetch or a
# concurrent caller never leaves a partial one at <repository>.
if ! git -C "$repository" rev-parse --quiet --verify "$rev^{commit}" > /dev/null 2>&1; then
  mkdir -p "$(dirname "$repository")"
  part=$(mktemp -d "$repository.part.XXXXXX")
  trap 'rm -rf "$part"' EXIT
  git init --quiet --bare "$part"
  git -C "$part" fetch --quiet --depth 2 "${RUST_CLIPPY_URL:-https://github.com/rust-lang/rust-clippy}" "$rev"
  git -C "$part" update-ref refs/heads/master "$rev"
  git -C "$part" symbolic-ref HEAD refs/heads/master
  rm -rf "$repository"
  mv -T "$part" "$repository" 2> /dev/null || [[ -d $repository ]]
  rm -rf "$part"
  trap - EXIT
fi

channel_at() {
  git -C "$repository" show "$1:rust-toolchain.toml" | sed -n 's/^channel = "\(.*\)"/\1/p'
}
pinned=$(channel_at "$rev")
if [[ $pinned != "$channel" ]]; then
  echo "rust-clippy $rev sets $pinned, the toolchain is $channel: run mise run toolchain:bump" >&2
  exit 1
fi
if [[ $(channel_at "$rev^") == "$pinned" ]]; then
  echo "rust-clippy $rev does not set $pinned: its parent names it too" >&2
  exit 1
fi

GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.$repository.insteadOf" GIT_CONFIG_VALUE_0=https://github.com/rust-lang/rust-clippy \
  exec "$@"
