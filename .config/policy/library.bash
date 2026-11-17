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
# bare repository beside it fetches each revision once. The script makes a
# new checkout in a scratch directory under a lock, and one `mv` puts it in
# place. So a reader finds a whole checkout, or none.
#
# Usage: library.bash <revision>
set -euo pipefail
revision=${1:?usage: library.bash <revision>}
[[ $revision =~ ^[0-9a-f]{40}$ ]] || { echo "library.bash: $revision is not a full revision" >&2; exit 2; }
url=https://github.com/gandr-lang/quenchant
cache=${XDG_CACHE_HOME:-$HOME/.cache}/gandr/quenchant
root=$cache/$revision
if [[ ! -d $root ]]; then
  mkdir -p "$cache"
  exec 8> "$cache/.lock"
  flock 8
  if [[ ! -d $root ]]; then
    repository=$cache/repository.git
    [[ -d $repository ]] || git init --quiet --bare "$repository"
    git --git-dir="$repository" cat-file -e "$revision^{commit}" 2> /dev/null \
      || git --git-dir="$repository" fetch --quiet "$url" "$revision"
    work=$(mktemp -d "$cache/.checkout.XXXXXX")
    git --git-dir="$repository" --work-tree="$work" checkout --quiet --force "$revision" -- .
    mv -T "$work" "$root"
  fi
  exec 8>&-
fi
printf '%s\n' "$root"
