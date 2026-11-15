#!/usr/bin/env bash
# One undefined-behaviour check over the crates that hold `unsafe` (#7642).
#
#   .config/unsafe/run.bash <check> [<package>...]
#
# `skips` compares each crate's skips with its list and runs no test. The
# landing's gate runs it (`check:unsafe-skips`), so a skip with no row fails
# before the landing and not at night.
#
# `miri-tree` and `miri-stacked` interpret each test under Miri, each with one
# aliasing model, with strict provenance and with the host's clock and files.
# `careful` runs each test natively against a standard library built with its
# debug assertions, with the implicit provenance casts denied. Each package is
# a crate of `.config/unsafe/crates.json`, and no package names every crate
# there.
#
# A test that Miri cannot run, or that costs too much under Miri, carries
# `#[cfg_attr(miri, ignore = "<reason>")]`. So nextest reports its name and its
# reason, and `careful` runs it natively. The list holds one skip for each such
# attribute, with the same reason, and the check refuses a crate whose skips
# and list differ. rustfmt puts an attribute with a long reason on four lines,
# so the check reads the attribute across lines.
# - see: `.config/unsafe/skips.jq`
set -euo pipefail
check=${1:?the check: skips, miri-tree, miri-stacked or careful}
shift
root=$(git rev-parse --show-toplevel)
list=$root/.config/unsafe/crates.json
if (($# == 0)); then
  mapfile -t crates < <(jq -r '.crates[].package' "$list")
else
  crates=("$@")
fi
packages=()
for crate in "${crates[@]}"; do
  path=$(jq -r --arg crate "$crate" '.crates[] | select(.package == $crate) | .path' "$list")
  if [[ -z $path ]]; then
    echo "unsafe:$check: \`$crate\` is no crate of $list" >&2
    exit 2
  fi
  if ! jq -n --arg crate "$crate" --arg list "$list" \
    --slurpfile stated <(jq -c --arg crate "$crate" '[.crates[] | select(.package == $crate) | .skips[].why]' "$list") \
    --slurpfile found <({ grep -rhzoP 'cfg_attr\(\s*miri,\s*ignore = "[^"]*",?\s*\)' "$root/$path" || true; } | tr '\0' '\n' | sed -nE 's/^.*ignore = "(.*)".*$/\1/p' | jq -Rsc 'split("\n") | map(select(. != ""))') \
    '{crate: $crate, list: $list, stated: $stated[0], found: $found[0]}' | jq -r -f "$root/.config/unsafe/skips.jq"; then
    echo "unsafe:$check: refused" >&2
    exit 1
  fi
  packages+=(--package "$crate")
done
case $check in
  skips)
    exit 0
    ;;
  miri-tree | miri-stacked)
    rustup component add miri rust-src
    flags=(-Zmiri-strict-provenance -Zmiri-disable-isolation)
    if [[ $check == miri-tree ]]; then
      flags+=(-Zmiri-tree-borrows)
    fi
    MIRIFLAGS="${flags[*]}" exec "$root/.config/mise/scope" cargo miri nextest run --locked --no-fail-fast "${packages[@]}"
    ;;
  careful)
    # The lint goes in as the test profile's flags, never as `RUSTFLAGS`:
    # Cargo reads `RUSTFLAGS` in place of the flags of `.cargo/config.toml`,
    # and profile flags add to them. cargo-careful builds against a standard
    # library of its own, so its build has a target directory of its own,
    # and the build of the native tests stays.
    rustup component add rust-src
    CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$root/target}/careful \
      CARGO_UNSTABLE_PROFILE_RUSTFLAGS=true \
      CARGO_PROFILE_TEST_RUSTFLAGS='-Zcrate-attr=feature(strict_provenance_lints) -Aunstable_features -Dimplicit_provenance_casts' \
      exec "$root/.config/mise/scope" cargo careful nextest run --locked --no-fail-fast "${packages[@]}"
    ;;
  *)
    echo "unsafe: no check \`$check\`: skips, miri-tree, miri-stacked or careful" >&2
    exit 2
    ;;
esac
