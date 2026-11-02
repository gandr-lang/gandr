#!/usr/bin/env bash
# Runs a command that builds a Dylint driver against a pinned rust-clippy:
#   rust-clippy.bash <repository> <channel> <command>…
# dylint_driver's build script clones rust-clippy, checks out the ref `main`
# and walks first parents back to the commit that set the toolchain's
# channel; it reads no pin of ours. The clone is served from <repository>, a
# local repository holding the pinned commit as `main`, through a rewrite
# scoped to the one command. The repository is fetched once, at depth 2, and
# kept: the walk stops at the commit's first parent, whose channel differs.
# The CI image's driver stage and `check:dylint` both run through here.
#
# The pin is the commit on the first-parent line of rust-clippy's
# rust-<stable> tag that set the channel, the tag quenchant's clippy_utils
# pins; `mise run toolchain:bump` moves it with the channel. A commit naming
# another channel than <channel>, or whose parent names the same, is refused.
# `RUST_CLIPPY_URL` names another source to fetch the commit from.
set -euo pipefail
# rust-clippy's rust-1.99.0, the commit that set nightly-2026-08-07.
rev=1a65e083e1c7c13503d79ed4d8e115888c845b19
(( $# > 2 )) || { echo 'usage: rust-clippy.bash <repository> <channel> <command>…' >&2; exit 2; }
repository=$1 channel=$2
shift 2

# A complete repository is renamed into place, so an interrupted fetch or a
# concurrent caller never leaves a partial one at <repository>. The rename is
# rename(2) through Perl, which every host and the image carry: it fails on a
# directory a concurrent caller placed first, as `mv -T` does, and darwin's
# `mv` has no `-T` (#3601). A failed rename passes only when <repository>
# then holds the pinned commit; otherwise it is refused with its cause.
if ! git -C "$repository" rev-parse --quiet --verify "$rev^{commit}" > /dev/null 2>&1; then
  mkdir -p "$(dirname "$repository")"
  part=$(mktemp -d "$repository.part.XXXXXX")
  trap 'rm -rf "$part"' EXIT
  git init --quiet --bare "$part"
  git -C "$part" fetch --quiet --depth 2 "${RUST_CLIPPY_URL:-https://github.com/rust-lang/rust-clippy}" "$rev"
  git -C "$part" update-ref refs/heads/main "$rev"
  git -C "$part" symbolic-ref HEAD refs/heads/main
  rm -rf "$repository"
  if ! moved=$(perl -e 'rename $ARGV[0], $ARGV[1] or die "$!\n"' "$part" "$repository" 2>&1) \
    && ! git -C "$repository" rev-parse --quiet --verify "$rev^{commit}" > /dev/null 2>&1; then
    echo "rust-clippy.bash: the fetched repository does not move to $repository: $moved" >&2
    exit 1
  fi
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
