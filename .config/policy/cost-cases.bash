#!/usr/bin/env bash
# The policy reads a `# Cost` bullet that the formatter wraps over two lines
# as one bullet (#7641). `check:dylint` runs the case after its own run,
# through its own command (`policy`). The case builds a scratch workspace of
# two packages. Each holds one function whose `# Cost` bullet takes two lines.
# The bullet of `cost-case-declared` declares an allocation, and the run over
# it passes. The bullet of `cost-case-refused` is in neither form, and the run
# over it names the whole bullet. The case runs with none of the policy's
# denied lints, so they ask nothing of the scratch function. The allocation
# lint is denied by its own default.
set -euo pipefail
declare -F policy > /dev/null || { echo "cost case: run it from check:dylint, which exports \`policy\`" >&2; exit 2; }
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "cost case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A library package `cost-case-$1`, its crate documented, that holds one
# documented function. Its `# Cost` bullet is the line `$2` and the line `$3`
# under it, as the formatter wraps a long bullet. The signature shows no
# primitive and the rustdoc states a specification, as the lints of the
# default demand.
package() {
  local name=$1 first=$2 second=$3
  mkdir -p "$scratch/$name/src"
  printf '[package]\nname = "cost-case-%s"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n' "$name" > "$scratch/$name/Cargo.toml"
  printf '//! A package of the cost case.\n\n/// A count of the case.\npub enum Count {\n    /// The one count.\n    One,\n}\n\n/// The count of the case.\n///\n/// # Specification\n/// trivial.\n///\n/// # Cost\n/// %s\n///   %s\npub fn count() -> Count {\n    Count::One\n}\n' "$first" "$second" > "$scratch/$name/src/lib.rs"
}

printf '[workspace]\nmembers = ["declared", "refused"]\nresolver = "3"\n' > "$scratch/Cargo.toml"
package declared '- allocation: the values of the case, one for each count, and the' 'frames of its walk, growth within the count'
package refused '- allocation: the values of the case, one for each count,' 'because it is simple'
cargo generate-lockfile --offline --quiet --manifest-path "$scratch/Cargo.toml"

# The records of the case's crates go to the scratch directory, never to the
# workspace's evidence. Cargo writes its output plain, so the case reads its
# lines as text.
configuration=$(printf '[quenchant-dylints]\nevidence_directory = "%s"\n' "$scratch/records")
run() {
  DYLINT_TOML=$configuration DYLINT_RUSTFLAGS='' CARGO_TERM_COLOR=never \
    policy --manifest-path "$scratch/Cargo.toml" --package "cost-case-$1" 2>&1
}

status=0
out=$(run declared) || status=$?
if [[ $status != 0 || $out == *"states an allocation in neither form"* ]]; then
  fail "#7641: a declared bullet that the formatter wraps reads as declared" "exit $status: $out"
fi
# The refusal quotes the two lines of the bullet as one.
whole="\`- allocation: the values of the case, one for each count, because it is simple\` states an allocation in neither form"
status=0
out=$(run refused) || status=$?
if [[ $status == 0 || $out != *"$whole"* ]]; then
  fail "#7641: a wrapped bullet in neither form is refused with the whole bullet" "exit $status: $out"
fi

(( failed == 0 )) || exit 1
echo "cost case OK: the policy reads a wrapped declared bullet as declared, and refuses a wrapped bullet in neither form with the whole bullet"
