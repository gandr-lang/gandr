#!/usr/bin/env bash
# `check:doc` for a target of another system (#7606). The items of some
# crates stand on Linux targets alone. Such a crate documents on a macOS host
# too, and its lead links no item that one set of targets holds alone. A
# seat's gate runs on one system, so this check documents each such crate for
# a target of the other system, with the flags of `check:doc`. The standard
# library of that target builds from `rust-src`, which `rust-toolchain.toml`
# pins.
#
# The crates:
#
# - `gandr-runtime-scope` and `gandr-runtime-uring`: the crate root stands
#   on Linux alone, and another system compiles it empty.
#
# Usage: targets-cases.bash
set -euo pipefail
root=$(cd "${BASH_SOURCE[0]%/*}/../.." && pwd)
case $(uname -s) in
  Linux) target=aarch64-apple-darwin ;;
  *) target=x86_64-unknown-linux-gnu ;;
esac
crates=(gandr-runtime-scope gandr-runtime-uring)
packages=()
for crate in "${crates[@]}"; do packages+=(--package "$crate"); done
export RUSTDOCFLAGS="-D warnings -Zunstable-options --check"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$root/target/gate-doc-targets}

failed=0
fail() {
  printf 'doc-targets: %s\n' "$*" >&2
  failed=1
}

# The two passes of `check:doc`: the default features, then every feature.
for features in default --all-features; do
  flags=()
  [[ $features == default ]] || flags=("$features")
  output=$(cd "$root" && "$root/.config/mise/gated" cargo doc "${packages[@]}" "${flags[@]}" \
    --locked --no-deps --document-private-items --target "$target" \
    -Zbuild-std=core,alloc,std,panic_abort 2>&1) \
    || fail "#7606: ${crates[*]} does not document for $target with the $features features: $output"
done

(( failed == 0 )) || exit 1
echo "doc-targets check OK: ${crates[*]} documents for $target with the default features and with every feature (#7606)"
