#!/usr/bin/env bash
# One undefined-behaviour check over the crates that hold `unsafe` (#7642).
#
#   .config/unsafe/run.bash <check> [<package>...]
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
# and list differ.
set -euo pipefail
check=${1:?the check: miri-tree, miri-stacked or careful}
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
  stated=$(jq -r --arg crate "$crate" '.crates[] | select(.package == $crate) | .skips[].why' "$list" | sort)
  found=$({ grep -rhoE 'cfg_attr\(miri, ignore = "[^"]*"\)' "$root/$path" || true; } | sed -E 's/^cfg_attr\(miri, ignore = "(.*)"\)$/\1/' | sort)
  if [[ $stated != "$found" ]]; then
    echo "unsafe:$check: the skips of \`$crate\` under Miri differ from $list; each skip in the crate is a row of its list, with the same reason (< the list, > the crate):" >&2
    diff <(printf '%s\n' "$stated") <(printf '%s\n' "$found") >&2 || true
    exit 1
  fi
  packages+=(--package "$crate")
done
case $check in
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
    echo "unsafe: no check \`$check\`: miri-tree, miri-stacked or careful" >&2
    exit 2
    ;;
esac
