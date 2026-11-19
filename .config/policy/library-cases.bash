#!/usr/bin/env bash
# A policy run writes nothing into the checkouts of the cargo home.
# `check:dylint` runs the case after its policy run, through its own command
# `policy`. By then the cargo home holds quenchant's checkouts, whose names
# the case takes. The case gives the run a cargo home of its own, with no
# network.
# - see: #7492
#
# That home holds a checkouts directory under each name of quenchant's
# checkouts in the cargo home of the gate. Each directory holds one empty
# checkout. A scratch workspace carries the library entry of this
# workspace's metadata. A run that resolves that entry writes a dummy crate
# into each empty checkout. The checkout then has a new time.
#
# The case reads only those times. The exit of the run tells it nothing.
#
# Dylint reads the metadata of the working directory. So the run starts in
# the scratch workspace. That workspace stands under `target`. So the run
# takes the lane of this tree, and its `.config` points at this tree's.
set -euo pipefail
declare -F policy > /dev/null || { echo "library case: run it from check:dylint, which exports \`policy\`" >&2; exit 2; }
mkdir -p target
scratch=$(mktemp -d "$PWD/target/library-case.XXXXXX")
trap 'rm -rf "$scratch"' EXIT

fail() {
  echo "library case FAILED: $1"
  echo "  got: $2"
  exit 1
}

# A revision root can survive an interrupted cache restore without its
# checkout. The library script must replace that root before it returns it.
fixture=$scratch/library-fixture
git init --quiet "$fixture"
git -C "$fixture" config user.email test@example.invalid
git -C "$fixture" config user.name test
mkdir -p "$fixture/crates/quenchant-dylints"
: > "$fixture/Cargo.toml"
: > "$fixture/crates/quenchant-dylints/Cargo.toml"
git -C "$fixture" add .
git -C "$fixture" commit --quiet -m fixture
revision=$(git -C "$fixture" rev-parse HEAD)
origin=$scratch/quenchant.git
git clone --quiet --bare "$fixture" "$origin"
cache=$scratch/library-cache
mkdir -p "$cache/gandr/quenchant/$revision"
global=$scratch/gitconfig
git config --file "$global" url."file://$origin".insteadOf https://github.com/gandr-lang/quenchant
fixture_library=$(GIT_CONFIG_GLOBAL="$global" XDG_CACHE_HOME="$cache" "$PWD/.config/policy/library.bash" "$revision")
[[ -d "$fixture_library/crates/quenchant-dylints" ]] \
  || fail "#8068: the library replaces an incomplete revision root" "$fixture_library has no crates/quenchant-dylints"
shopt -s nullglob
names=("${CARGO_HOME:-$HOME/.cargo}"/git/checkouts/quenchant-*)
shopt -u nullglob
if (( ${#names[@]} == 0 )); then
  fail "#7492: the cargo home holds a checkout of quenchant, whose names the case takes" "no checkouts directory of quenchant"
fi
home=$scratch/cargo-home
checkouts=()
for name in "${names[@]}"; do
  mkdir -p "$home/git/checkouts/${name##*/}/case"
  checkouts+=("$home/git/checkouts/${name##*/}/case")
done
times() { stat -c '%n %y' "${checkouts[@]}"; }
before=$(times)

libraries=$(cargo metadata --no-deps --format-version 1 --locked | jq -r '
  .metadata.dylint.libraries[]
  | "[[workspace.metadata.dylint.libraries]]\ngit = \(.git | tojson)\nrev = \(.rev | tojson)\npattern = \(.pattern | tojson)\n"')
mkdir -p "$scratch/workspace/src"
printf '[package]\nname = "library-case"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n\n[workspace]\n\n%s' \
  "$libraries" > "$scratch/workspace/Cargo.toml"
: > "$scratch/workspace/src/lib.rs"
ln -s "$PWD/.config" "$scratch/workspace/.config"
cp rust-toolchain.toml "$scratch/workspace/"
(
  cd "$scratch/workspace"
  CARGO_HOME=$home CARGO_NET_OFFLINE=true CARGO_TERM_COLOR=never policy --package library-case > "$scratch/run.txt" 2>&1
) || true

after=$(times)
if [[ $after != "$before" ]]; then
  fail "#7492: the policy run writes into the checkouts of its cargo home" \
    "$(diff <(echo "$before") <(echo "$after") | grep -c '^>') of ${#checkouts[@]} checkouts with a new time"
fi
echo "library case OK: the policy run writes nothing into the ${#checkouts[@]} checkouts of its cargo home"
