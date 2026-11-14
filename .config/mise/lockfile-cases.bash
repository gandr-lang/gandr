#!/usr/bin/env bash
# The cases of `check:lockfile` (#7541), over the real mise. A scratch tree
# reads its rust pin from `rust-toolchain.toml`, as the tree does, and its
# lock holds the tree's own rust entry. A lock whose rust entry is the pin
# passes the locked install. A lock whose rust entry is another nightly is
# refused, and mise names the pin. The install that `toolchain:bump` runs
# after it writes the pin writes the pin's entry, and the locked install of
# that tree then passes. Where mise takes no rust pin, the check installs no
# rust and runs no case.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
fail() {
  printf 'check:lockfile case FAILED: %s\n  wanted: %s\n  got:    %s\n' "$1" "$2" "$3" >&2
  failed=1
}
# Each scratch tree takes its pin from `rust-toolchain.toml`, whatever the
# caller's mise takes: the variable replaces the setting of `mise.toml`.
export MISE_IDIOMATIC_VERSION_FILE_ENABLE_TOOLS=rust
channel=$(sed -n 's/^channel = "\([^"]*\)".*/\1/p' "$root/rust-toolchain.toml")
# A tree that pins the tree's toolchain. Its lock holds the tree's rust entry,
# with the version `$2`.
tree() {
  local dir=$scratch/$1
  mkdir -p "$dir"
  cp "$root/rust-toolchain.toml" "$dir/"
  printf '[settings]\nlockfile = true\nidiomatic_version_file_enable_tools = ["rust"]\n' > "$dir/mise.toml"
  {
    printf 'lockfile_version = 3\n\n'
    awk '/^\[\[tools\.rust\]\]$/ { take = 1; print; next } take && /^\[\[/ { exit } take' "$root/mise.lock"
  } | sed "s/\"$channel\"/\"$2\"/g" > "$dir/mise.lock"
  printf '%s\n' "$dir"
}
# The locked install of rust in `$1`: its status. Its output goes to the
# file `out` of the scratch directory.
outcome() {
  local status=0
  (cd "$1" && MISE_TRUSTED_CONFIG_PATHS=$1 mise install --locked rust) > "$scratch/out" 2>&1 || status=$?
  echo "exit $status"
}
same=$(tree same "$channel")
got=$(outcome "$same")
[[ $got == "exit 0" ]] || fail "a lock whose rust entry is the pin passes the locked install" "exit 0" "$got: $(< "$scratch/out")"

stale=$(tree stale nightly-2000-01-01)
got=$(outcome "$stale")
[[ $got != "exit 0" ]] || fail "#7541: a lock whose rust entry is not the pin is refused" "a nonzero exit" "$got"
named=$(< "$scratch/out")
[[ $named == *"rust@$channel is not in the lockfile"* ]] \
  || fail "#7541: the refusal names the pin" "rust@$channel is not in the lockfile" "$named"

# The step of `toolchain:bump` after it writes the pin: an install without
# --locked, which writes the entry of the pin into the lock.
(cd "$stale" && MISE_TRUSTED_CONFIG_PATHS=$stale mise install rust) > "$scratch/out" 2>&1 \
  || fail "#7541: the install of the bump runs" "exit 0" "$(< "$scratch/out")"
got=$(outcome "$stale")
[[ $got == "exit 0" ]] \
  || fail "#7541: the install of the bump writes the entry of the pin, so the locked install passes" "exit 0" "$got: $(< "$scratch/out")"

# The CI image gives the variable the empty value and leaves rust to rustup.
# There the check installs no rust and runs no case (#7548).
status=0
got=$(cd "$root" && MISE_IDIOMATIC_VERSION_FILE_ENABLE_TOOLS='' mise run --quiet check:lockfile 2>&1) || status=$?
[[ $status == 0 && $got != *"rust@"* ]] \
  || fail "#7548: where mise takes no rust pin, check:lockfile installs no rust" "exit 0, no rust install" "exit $status: $got"

(( failed == 0 )) || exit 1
echo "check:lockfile cases OK: the pin's entry passes, another nightly's entry is refused and the pin named, the bump's install writes the pin's entry, and the check installs no rust where mise takes no rust pin"
