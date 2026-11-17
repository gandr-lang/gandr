#!/usr/bin/env bash
# A run with a base lints again each package whose base's records change,
# after a run that leaves its results fresh with no base (#7640).
# `check:dylint` runs the case after its own run, through its own command
# (`policy`). The case builds a scratch workspace of one package, whose one
# function allocates and declares no allocation. The first run has no base,
# so the lint holds nothing and the run passes. Then a base record gives the
# function another body, and `fresh.bash` reads it. The second run holds the
# function as changed and refuses its allocation by name. A third read of the
# same records cleans no package. The case runs with none of the policy's
# denied lints, so they ask nothing of the scratch function. The allocation
# lint is denied by its own default.
set -euo pipefail
declare -F policy > /dev/null || { echo "fresh case: run it from check:dylint, which exports \`policy\`" >&2; exit 2; }
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "fresh case FAILED: $1"
  echo "  got: $2"
  failed=1
}

printf '[workspace]\nmembers = ["grow"]\nresolver = "3"\n' > "$scratch/Cargo.toml"
mkdir -p "$scratch/grow/src" "$scratch/base"
printf '[package]\nname = "fresh-case-grow"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n' > "$scratch/grow/Cargo.toml"
# The function allocates through `vec!`. Its signature shows no primitive,
# its type is no struct of one field, and its rustdoc states a
# specification, as the lints of the default demand.
printf '//! A package of the fresh case.\n\n/// A value of the case.\npub enum Value {\n    /// The first.\n    One,\n    /// The second.\n    Two,\n}\n\n/// The two values of the case.\n///\n/// # Specification\n/// trivial.\npub fn values() -> Vec<Value> {\n    vec![Value::One, Value::Two]\n}\n' > "$scratch/grow/src/lib.rs"
cargo generate-lockfile --offline --quiet --manifest-path "$scratch/Cargo.toml"

# The records of the case's crate go to the scratch directory, never to the
# workspace's evidence. Cargo writes its output plain, so the case reads its
# lines as text.
configuration=$(printf '[quenchant-dylints]\nevidence_directory = "%s"\nallocation_base_records = "%s"\n' "$scratch/records" "$scratch/base")
run() {
  DYLINT_TOML=$configuration DYLINT_RUSTFLAGS='' CARGO_TERM_COLOR=never \
    policy --manifest-path "$scratch/Cargo.toml" --package fresh-case-grow 2>&1
}
# `cargo dylint` builds the scratch workspace in the check targets of this
# tree, so the case cleans those, with a stamp of its own.
fresh() {
  "$here/fresh.bash" "$scratch/base" "$scratch/stamp" target/dylint "$scratch/Cargo.toml" 2>&1
}
refusal="reaches a call into the allocator"

fresh > /dev/null
status=0
out=$(run) || status=$?
if [[ $status != 0 || $out == *"$refusal"* ]]; then
  fail "#7640: a run with no base holds no function and passes" "exit $status: $out"
fi

# The base's record of the unit: each function of the head's record, with
# another body of the same scheme.
shopt -s nullglob
units=("$scratch"/records/*.lib.jsonl)
shopt -u nullglob
if (( ${#units[@]} != 1 )); then
  fail "#7640: the run with no base writes one record of the library" "${#units[@]} records: ${units[*]}"
else
  jq -c 'select(.record == "item" and (.kind == "fn" or .kind == "assoc-fn")) | .body |= (split("-")[0] + "-0")' "${units[0]}" > "$scratch/base/${units[0]##*/}"
  read=$(fresh)
  if [[ $read != "fresh: 1 packages lint again, as their base's records change: fresh-case-grow" ]]; then
    fail "#7640: a new base record names its package to lint again" "$read"
  fi
  status=0
  out=$(run) || status=$?
  if [[ $status == 0 || $out != *"$refusal"* ]]; then
    fail "#7640: the run with a base after a run with none refuses the allocation by name" "exit $status: $out"
  fi
  read=$(fresh)
  if [[ $read != "fresh: 0 packages lint again, as their base's records change" ]]; then
    fail "#7640: the same base's records keep each fresh result" "$read"
  fi
fi

(( failed == 0 )) || exit 1
echo "fresh case OK: a run with a base after a run with none lints its package again and refuses by name, and the same records keep each fresh result"
