#!/usr/bin/env bash
# The policy refuses a trait object of a configured class, and a reasoned
# `expect` at the site keeps it (#7384). `check:dylint` runs the case after
# its own run, through its own command (`policy`). The case builds a scratch
# workspace of two packages. Each holds one static trait object of
# `core::fmt::Display`, and the configuration names that trait as a class.
# The run over `trait-object-case-refused` fails and names the lint. The run
# over `trait-object-case-kept`, whose static carries the `expect`, passes.
set -euo pipefail
declare -F policy > /dev/null || { echo "trait-object case: run it from check:dylint, which exports \`policy\`" >&2; exit 2; }
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "trait-object case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A library package `trait-object-case-$1`, its crate documented, that holds
# one documented static trait object, with the attribute line `$2` above it.
package() {
  local name=$1 attribute=$2
  mkdir -p "$scratch/$name/src"
  printf '[package]\nname = "trait-object-case-%s"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n' "$name" > "$scratch/$name/Cargo.toml"
  printf '//! A package of the trait-object case.\n\n/// A shown value of the case.\n%s\npub static SHOWN: &(dyn core::fmt::Display + Sync) = &1_u32;\n' "$attribute" > "$scratch/$name/src/lib.rs"
}

printf '[workspace]\nmembers = ["refused", "kept"]\nresolver = "3"\n' > "$scratch/Cargo.toml"
package refused ''
package kept '#[cfg_attr(dylint_lib = "quenchant_dylints", expect(trait_object, reason = "the case keeps one trait object"))]'
cargo generate-lockfile --offline --quiet --manifest-path "$scratch/Cargo.toml"

# The records of the case's crates go to the scratch directory, never to the
# workspace's evidence. Cargo writes its output plain, so the case reads its
# lines as text.
configuration=$(printf '[quenchant-dylints]\nevidence_directory = "%s"\ntrait_object_classes = ["core::fmt::Display"]\n' "$scratch/records")
run() {
  DYLINT_TOML=$configuration CARGO_TERM_COLOR=never \
    policy --manifest-path "$scratch/Cargo.toml" --package "trait-object-case-$1" 2>&1
}

status=0
out=$(run refused) || status=$?
if [[ $status == 0 || $out != *"is a trait object of a configured class"* ]]; then
  fail "#7384: the policy refuses a trait object of a configured class by name" "exit $status: $out"
fi
status=0
out=$(run kept) || status=$?
if [[ $status != 0 || $out == *"is a trait object of a configured class"* ]]; then
  fail "#7384: a reasoned expect at the site keeps its trait object" "exit $status: $out"
fi

(( failed == 0 )) || exit 1
echo "trait-object case OK: the policy refuses a configured class by name, and a reasoned expect keeps its site"
