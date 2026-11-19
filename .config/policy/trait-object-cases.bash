#!/usr/bin/env bash
# The policy refuses a trait object of a configured class, and a reasoned
# `expect` at the site keeps it. `check:dylint` runs the case after its own
# run, through its own command, `policy`. The case builds a scratch workspace
# of five packages.
# - see: #7384
#
# Two packages hold one static trait object of `core::fmt::Display`, and the
# configuration names that trait as a class. The run over
# `trait-object-case-refused` fails and names the lint. The run over
# `trait-object-case-kept`, whose static carries the `expect`, passes.
#
# Two more hold a static `dyn Fn` and a static `dyn FnMut`. The configuration
# names `core::ops::Fn` and `core::ops::FnMut` as the workspace does. The last
# holds a static `dyn std::io::Write`, and the configuration names
# `std::io::Write` as the workspace does. Each of the last three runs fails
# and names the lint. So a class path that resolves to no trait fails the case.
# - see: #7386, #7387
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
# the documented static `$3`, with the attribute line `$2` above it.
package() {
  local name=$1 attribute=$2 item=$3
  mkdir -p "$scratch/$name/src"
  printf '[package]\nname = "trait-object-case-%s"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n' "$name" > "$scratch/$name/Cargo.toml"
  printf '//! A package of the trait-object case.\n\n/// A value of the case.\n%s\n%s\n' "$attribute" "$item" > "$scratch/$name/src/lib.rs"
}

shown='pub static SHOWN: &(dyn core::fmt::Display + Sync) = &1_u32;'
printf '[workspace]\nmembers = ["refused", "kept", "called", "moved", "written"]\nresolver = "3"\n' > "$scratch/Cargo.toml"
package refused '' "$shown"
package kept '#[cfg_attr(dylint_lib = "quenchant_dylints", expect(trait_object, reason = "the case keeps one trait object"))]' "$shown"
package called '' 'pub static CALLED: &(dyn Fn() + Sync) = &|| {};'
package moved '' 'pub static MOVED: &(dyn FnMut() + Sync) = &|| {};'
package written '' 'pub static WRITTEN: &(dyn std::io::Write + Sync) = &std::io::empty();'
cargo generate-lockfile --offline --quiet --manifest-path "$scratch/Cargo.toml"

# The records of the case's crates go to the scratch directory, never to the
# workspace's evidence. Cargo writes its output plain, so the case reads its
# lines as text.
configuration=$(printf '[quenchant-dylints]\nevidence_directory = "%s"\ntrait_object_classes = ["core::fmt::Display", "core::ops::Fn", "core::ops::FnMut", "std::io::Write"]\n' "$scratch/records")
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
for name in called moved; do
  status=0
  out=$(run "$name") || status=$?
  if [[ $status == 0 || $out != *"is a trait object of a configured class"* ]]; then
    fail "#7386: the policy refuses the $name callback by its class path" "exit $status: $out"
  fi
done
status=0
out=$(run written) || status=$?
if [[ $status == 0 || $out != *"is a trait object of a configured class"* ]]; then
  fail "#7387: the policy refuses the writer by its class path" "exit $status: $out"
fi

(( failed == 0 )) || exit 1
echo "trait-object case OK: the policy refuses each configured class by name, the callbacks' and the writer's paths among them, and a reasoned expect keeps its site"
