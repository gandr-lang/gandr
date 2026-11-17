#!/usr/bin/env bash
# These cases pin the daemons of two jobs that run at one time on one host.
# Each job writes its wrapper under a `RUNNER_TEMP` of its own. Both jobs
# share one cache directory, as two runners of one account do. Each job
# starts its daemon through its wrapper. The end of the first job stops its
# daemon, and the daemon of the second job stays alive.
# - see: #7828 — one daemon for each job
# - see: `.github/actions/setup-rust/kache-wrapper.bash`
#
# The cases run where kache is: mise installs it from the pin.
set -euo pipefail
tree=$(cd "${BASH_SOURCE[0]%/*}/../.." && pwd)
here=$tree/.github/actions/setup-rust
if ! command -v kache > /dev/null 2>&1; then
  echo "kache-wrapper check skipped: this host has no kache"
  exit 0
fi
scratch=$(mktemp -d)
wrappers=()
cleanup() {
  local wrapper
  for wrapper in "${wrappers[@]}"; do "$wrapper" daemon stop > /dev/null 2>&1 || true; done
  rm -rf "$scratch"
}
trap cleanup EXIT
# The daemons of the cases keep their cache apart from the host's.
export KACHE_CACHE_DIR=$scratch/cache
failed=0
fail() {
  echo "kache-wrapper check FAILED: $1" >&2
  failed=1
}

# Whether the daemon of the wrapper `$1` runs.
running() {
  "$1" daemon status --json | jq -e '.daemon_running' > /dev/null
}

if [[ ${OSTYPE:-} == darwin* ]]; then
  fake=$scratch/no-kache
  mkdir -p "$fake"
  printf '#!/usr/bin/env bash\nexit 1\n' > "$fake/kache"
  chmod +x "$fake/kache"
  read -r toolchain _ < <(rustup show active-toolchain)
  driver=$HOME/.dylint_drivers/$toolchain/dylint-driver
  rustc=$(rustup which rustc)
  if [[ ! -x $driver ]]; then
    fail "#7861: no Dylint driver matches the active toolchain"
  elif ! PATH=$fake:$PATH RUSTUP_TOOLCHAIN=$toolchain "$tree/.config/kache/rustc-wrapper" "$driver" "$rustc" -V > /dev/null 2>&1; then
    fail "#7861: the tree wrapper did not load the Dylint driver"
  fi
else
  echo "kache-wrapper case skipped: #7861 Dylint driver library path needs macOS"
fi

for job in first second; do
  mkdir -p "$scratch/$job"
  wrapper=$(RUNNER_TEMP=$scratch/$job KACHE_TRUSTED=false KACHE_USER=case KACHE_TOKEN=case "$here/kache-wrapper.bash")
  wrappers+=("$wrapper")
  "$wrapper" daemon start > /dev/null
done
first=${wrappers[0]}
second=${wrappers[1]}
running "$first" || fail "#7828: the first job's wrapper started no daemon"
running "$second" || fail "#7828: the second job's wrapper started no daemon"
[[ $("$first" daemon status --json | jq -r .socket) != "$("$second" daemon status --json | jq -r .socket)" ]] \
  || fail "#7828: two jobs at one time resolve one socket, so they share one daemon"
"$first" daemon stop > /dev/null
! running "$first" || fail "#7828: the first job's drain left its daemon running"
running "$second" || fail "#7828: the end of the first job stopped the daemon of the second job"

((failed == 0)) || exit 1
echo "kache-wrapper check OK: two jobs at one time each ran a daemon of their own, and the end of one left the other's running"
