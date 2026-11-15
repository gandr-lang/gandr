#!/usr/bin/env bash
# The cold build of the night's chain report (#6893), one architecture's
# half: `nightly-sweeps.yml`'s `chain` and `chain-riscv64` run it, and a seat can run
# it on a host by hand. It builds the driver, `gandr-lang`, in the dev profile
# into an empty target directory under `<out>`, under the flags of
# `.cargo/config.toml` (#6882). Cargo's build analysis log records every unit
# with its edges and its times, and `-Zsection-timings` adds the start of
# each unit's code generation. The script keeps that log as `<out>/build.jsonl`,
# the timings report as `<out>/cargo-timing.html`, the commit as `<out>/head`
# and the machine as `<out>/machine`: the processor and its width, since two
# nights compare only on one machine. Then it removes the target directory.
# `report:chain` reads the log into the night's row. So the script needs
# only Cargo and the shell, as the riscv64 runner holds no mise.
#
#   chain-build.bash <arch> <out>
#
# `CHAIN_LOCK` names a host lock that the build holds while it runs, as the
# riscv64 host's measures hold `par` (#6945): a measure beside the build
# loads both. The measuring account owns the lock file, so the script opens
# it to read, creates none, and waits while another holder has it.
set -euo pipefail
arch=${1:?chain-build.bash <arch> <out>}
mkdir -p "${2:?chain-build.bash <arch> <out>}"
out=$(cd "$2" && pwd -P)
if [[ -n ${CHAIN_LOCK:-} && -e $CHAIN_LOCK ]]; then
  exec 9< "$CHAIN_LOCK"
  flock -n 9 || { echo "chain-build: a measure holds the host lock $CHAIN_LOCK, and the $arch build waits for it" >&2; flock 9; }
fi
logs=${CARGO_HOME:-$HOME/.cargo}/log
mkdir -p "$logs"
rm -rf "$out/target"
touch "$out/started"
CARGO_TARGET_DIR=$out/target cargo build --timings --locked --package gandr-lang \
  -Zbuild-analysis -Zsection-timings --config build.analysis.enabled=true >&2
# The log of this build is the newest one since the start that names this
# checkout as its directory. Cargo writes no `/` escaped in the JSON.
log=$(find "$logs" -name '*.jsonl' -newer "$out/started" -exec grep -l -F "\"cwd\":\"$PWD\"" {} + | sort | tail -n 1)
[[ -n $log ]] || { echo "chain-build: Cargo wrote no build analysis log for $PWD" >&2; exit 1; }
cp "$log" "$out/build.jsonl"
cp "$out/target/cargo-timings/cargo-timing.html" "$out/cargo-timing.html"
git rev-parse HEAD > "$out/head"
if [[ -r /proc/cpuinfo ]]; then
  processor=$(awk -F': ' '/^(model name|uarch)[[:space:]]*:/ { print $2; exit }' /proc/cpuinfo)
else
  processor=$(sysctl -n machdep.cpu.brand_string)
fi
printf '%s, %s threads, %s\n' "$(uname -m)" "$(getconf _NPROCESSORS_ONLN)" "${processor:-a processor it does not name}" > "$out/machine"
rm -rf "$out/target" "$out/started"
echo "chain-build: the $arch build log of $(cut -c1-9 "$out/head") is in $out" >&2
