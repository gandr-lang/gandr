#!/usr/bin/env bash
# A crate of the containers' wave with one `std` site left fails the gate by
# name (#7378). `check:dylint` runs the case after its own run, through its
# own command (`policy`). The case takes the line `std_container_crates` from
# the policy's own configuration, so the case reads the list that the gate
# reads. It builds a scratch workspace of two packages that hold the same
# function, whose signature names a `Vec` of `alloc`. The first package takes
# the name of the first crate of the list, and the run over it fails with the
# lint's refusal and the crate's name. The second package is in no list, and
# the run over it passes. The case runs with none of the policy's denied
# lints, so they ask nothing of the scratch function. The lint
# `std_container` is denied by its own default.
set -euo pipefail
declare -F policy > /dev/null || { echo "container case: run it from check:dylint, which exports \`policy\`" >&2; exit 2; }
listed=$(awk '/^std_container_crates = /' <<< "${DYLINT_TOML:?container case: run it from check:dylint, which sets DYLINT_TOML}")
first=${listed#*\"}
first=${first%%\"*}
[[ -n $listed && $first != "$listed" && -n $first ]] || { echo "container case: the policy lists no crate under \`std_container_crates\`" >&2; exit 2; }
# A prefix takes the name it starts with, so the name without its `*` is a
# crate of the list too.
package=${first%\*}
package=${package//_/-}
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "container case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A library package of name `$2` in the directory `$1`, its crate documented,
# that holds one documented function. The function hands back a `Vec`. The
# signature shows no primitive and the rustdoc states a specification, as the
# lints of the default demand.
package() {
  local directory=$1 name=$2
  mkdir -p "$scratch/$directory/src"
  printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n' "$name" > "$scratch/$directory/Cargo.toml"
  printf '//! A package of the container case.\n\n/// A count of the case.\npub enum Count {\n    /// The one count.\n    One,\n}\n\n/// The counts of the case.\n///\n/// # Specification\n/// trivial.\npub fn counts() -> Vec<Count> {\n    Vec::new()\n}\n' > "$scratch/$directory/src/lib.rs"
}

printf '[workspace]\nmembers = ["listed", "unlisted"]\nresolver = "3"\n' > "$scratch/Cargo.toml"
package listed "$package"
package unlisted container-case-unlisted
cargo generate-lockfile --offline --quiet --manifest-path "$scratch/Cargo.toml"

# The records of the case's crates go to the scratch directory, never to the
# workspace's evidence. Cargo writes its output plain, so the case reads its
# lines as text.
configuration=$(printf '[quenchant-dylints]\nevidence_directory = "%s"\n%s\n' "$scratch/records" "$listed")
run() {
  DYLINT_TOML=$configuration DYLINT_RUSTFLAGS='' CARGO_TERM_COLOR=never \
    policy --manifest-path "$scratch/Cargo.toml" --package "$1" 2>&1
}

refusal="\`Vec\` of \`alloc\` in a crate whose containers are its own"
status=0
out=$(run "$package") || status=$?
if [[ $status == 0 || $out != *"$refusal"* || $out != *"could not compile \`$package\`"* ]]; then
  fail "#7378: a std site left in a crate of the wave fails the gate by name" "exit $status: $out"
fi
status=0
out=$(run container-case-unlisted) || status=$?
if [[ $status != 0 || $out == *"$refusal"* ]]; then
  fail "#7378: a crate in no list keeps its std site" "exit $status: $out"
fi

(( failed == 0 )) || exit 1
echo "container case OK: a std site left in \`$package\` fails the gate by name, and a crate in no list keeps its site"
