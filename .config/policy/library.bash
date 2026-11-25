#!/usr/bin/env bash
# Prints the root of a checkout of quenchant at <revision>. `cargo dylint
# --path <root>` loads the lint library from that root. With `--path`,
# Dylint reads no library entry of the workspace metadata.
#
# Dylint resolves a git library of the workspace metadata through the cargo
# home. It puts a dummy crate into each checkout of that repository there,
# and then it removes the crate. Another cargo that reads one of those
# checkouts at that moment fails with `os error 2`.
# - see: #7492
#
# So each run of the policy loads the library from a checkout of its own.
# The checkout stands under the cache directory, one for each revision. A
# bare repository beside it fetches each revision once. A root is ready only
# when it holds the lint crate. The script replaces an incomplete root under
# the existing lock, then one `mv` puts the complete checkout in place.
#
# Usage: library.bash <revision>
set -euo pipefail
revision=${1:?usage: library.bash <revision>}
[[ $revision =~ ^[0-9a-f]{40}$ ]] || { echo "library.bash: $revision is not a full revision" >&2; exit 2; }
url=https://github.com/gandr-lang/quenchant
cache=${XDG_CACHE_HOME:-$HOME/.cache}/gandr/quenchant
root=$cache/$revision
ready=$root/crates/quenchant-dylints
if [[ ! -d $ready ]]; then
  mkdir -p "$cache"
  exec 8> "$cache/.lock"
  flock 8
  if [[ ! -d $ready ]]; then
    rm -rf "$root"
    repository=$cache/repository.git
    [[ -d $repository ]] || git init --quiet --bare "$repository"
    git --git-dir="$repository" cat-file -e "$revision^{commit}" 2> /dev/null \
      || git --git-dir="$repository" fetch --quiet "$url" "$revision"
    work=$(mktemp -d "$cache/.checkout.XXXXXX")
    git --git-dir="$repository" --work-tree="$work" checkout --quiet --force "$revision" -- .
    mv -T "$work" "$root"
    [[ -d $ready ]] || { echo "library.bash: $revision has no crates/quenchant-dylints" >&2; exit 1; }
  fi
  exec 8>&-
fi
printf '%s\n' "$root"
