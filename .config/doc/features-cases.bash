#!/usr/bin/env bash
# The two passes of `check:doc` (#6508). Each case documents a scratch crate
# through `check:doc` itself, with `GATE_SCOPE` set to the crate's manifest.
# The crate's module documentation links `Gate::ONLY`, and the case puts a
# `cfg` on that item:
#
# - no `cfg`: the link resolves under each set of features, and the gate
#   passes.
# - `cfg(feature = "extra")`: the link resolves with every feature on alone,
#   and the pass with the default features refuses it.
# - `cfg(not(feature = "extra"))`: the link resolves with the default features
#   alone, and the pass with every feature on refuses it.
set -euo pipefail
root=$(cd "${BASH_SOURCE[0]%/*}/../.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

failed=0
fail() {
  printf 'doc-features: %s\n' "$*" >&2
  failed=1
}

# A scratch crate in <dir> whose `Gate::ONLY` carries the attribute <cfg>.
crate() {
  mkdir -p "$1/src"
  printf '[package]\nname = "scratch"\nversion = "0.0.0"\nedition = "2024"\n\n[features]\nextra = []\n\n[workspace]\n' > "$1/Cargo.toml"
  printf '//! The constant [`Gate::ONLY`].\n\n/// A gate.\npub struct Gate;\n\n%s\nimpl Gate\n{\n    /// The only value.\n    pub const ONLY: u8 = 0;\n}\n' "$2" > "$1/src/lib.rs"
  cargo generate-lockfile --offline --quiet --manifest-path "$1/Cargo.toml"
}

# `check:doc` over the scratch crate in <dir>, inside a gate slot so that it
# takes none of the host's.
doc() {
  (cd "$root" && GANDR_GATE_SLOT=case GATE_SCOPE="--manifest-path $1/Cargo.toml" \
    CARGO_TARGET_DIR="$scratch/target" mise run --quiet check:doc 2>&1)
}

crate "$scratch/every" ''
output=$(doc "$scratch/every") || fail "#6508: a link that resolves under each set of features was refused: $output"

crate "$scratch/extra" '#[cfg(feature = "extra")]'
if output=$(doc "$scratch/extra"); then
  fail "#6508: a link to an item that the feature extra holds passed check:doc"
elif [[ $output != *'unresolved link to `Gate::ONLY`'* ]]; then
  fail "#6508: a link to an item that the feature extra holds was refused for another reason: $output"
fi

crate "$scratch/default" '#[cfg(not(feature = "extra"))]'
if output=$(doc "$scratch/default"); then
  fail "#6508: a link to an item that the feature extra removes passed check:doc"
elif [[ $output != *'unresolved link to `Gate::ONLY`'* ]]; then
  fail "#6508: a link to an item that the feature extra removes was refused for another reason: $output"
fi

(( failed == 0 )) || exit 1
echo "doc-features check OK: check:doc passed a link that resolves under each set of features and refused a link that resolves under one set alone, in each direction"
