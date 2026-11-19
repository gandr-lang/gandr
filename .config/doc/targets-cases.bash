#!/usr/bin/env bash
# The gate documents one target that differs from the gate's system. Some
# crate items stand on Linux alone.
#
# A macOS gate delegates the Linux pass to the configured Linux host. That
# host documents the committed tree. It does not build a Linux C library on
# macOS. A Linux gate documents the macOS target.
#
# The standard library of the other target builds from `rust-src`.
# `rust-toolchain.toml` pins it.
#
# - see: #7606
#
# The crates:
#
# - `gandr-runtime-scope` and `gandr-runtime-uring`: the crate root stands
#   on Linux alone, and another system compiles it empty.
#
# Usage: targets-cases.bash
set -euo pipefail
root=$(cd "${BASH_SOURCE[0]%/*}/../.." && pwd)
if [[ $(uname -s) != Linux && -z ${GANDR_DOC_TARGETS_NATIVE:-} ]]; then
  exec "$root/.config/doc/targets-remote.bash"
fi
if [[ ${GANDR_DOC_TARGETS_NATIVE:-} == 1 ]]; then
  target=native-Linux
  target_flags=()
  build_std=()
else
  case $(uname -s) in
    Linux) target=aarch64-apple-darwin ;;
    *) target=x86_64-unknown-linux-gnu ;;
  esac
  target_flags=(--target "$target")
  build_std=("-Zbuild-std=core,alloc,std,panic_abort")
fi
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
    --locked --no-deps --document-private-items "${target_flags[@]}" "${build_std[@]}" 2>&1) \
    || fail "#8091: ${crates[*]} does not document for $target with the $features features (#7606): $output"
done

(( failed == 0 )) || exit 1
echo "doc-targets check OK: ${crates[*]} documents for $target with the default features and with every feature (#7606)"
