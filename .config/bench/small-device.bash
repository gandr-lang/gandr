#!/usr/bin/env bash
# The small-device measure (#7308): four paths of gandr, each under a bound of
# cores and of memory, with its wall time, the time to its first line of
# output, its peak resident set, the peak that its scope charged and why it
# stopped. `bench:small-device` runs it, and `small-device.jq` writes each row.
# Before those rows come the counts of each check (#7359): the allocations of
# every thread and the frames that the kernel's checks pop, which the count
# build prints (`small-device-counts.jq`), and then the bytes of each frame of
# the kernel's checks, which rustc reads (`small-device-frames.jq`). A device
# fails on the allocation and not on the average, so the counts come first.
#
#   small-device.bash <gandr> <counting> <sizes> [<limit>]
#                                         measure the binary <gandr>
#   small-device.bash --check-host        refuse a host that cannot bound
#
# <gandr> is a build of this checkout: a driver reads `library/std` of the tree
# that it was built from, so over another tree the recheck refuses the
# declarations that name a host interface of `std`. <counting> is a build of
# the same checkout with the `counts` feature, which gives `check --counts`.
# <sizes> is the text that rustc prints for `gandr-kernel-core` under
# `-Zprint-type-sizes`.
#
# The paths, from the root of the checkout:
#   - a built program runs: `run corpus/model/effects/hello.gandr`;
#   - the kernel replays one source with no recorded verdict: `check
#     --recheck library/std/src/cost.gandr`, which checks its package;
#   - a small module checks cold: `check
#     crates/surface-corpus/strict/functions.gandr`;
#   - a crossing: `host` of `corpus/model/deployments/offers.gandr` serves the
#     world `far` under the bound, and an unbounded `run` of the same source
#     under its manifold ships the migration to it. The host replays nothing of
#     the entry that crosses, so its row times the hosting whole, from its
#     start to its exit. The host answers the console that the row of `far`
#     names from its own authority, so the migration prints at the host, and
#     the run ends.
#
# Each path runs once at each bound: 1 and 2 cores, and 64 MiB, 256 MiB and
# 1 GiB of memory. Each check of the count build runs once at 1 and 2 cores,
# under 1 GiB. A user scope of systemd holds the memory bound, with no swap.
# `taskset` holds the cores, since a user manager gives its scopes no `cpuset`
# controller and so ignores `AllowedCPUs`. Each run reads scratch
# configuration, cache and data directories, so it reads no verdict and no
# toolchain, and `<limit>` seconds bound its wall time, 300 unless given. Each
# run also sets `GANDR_TOOLCHAIN_HANDOFF=never`, so it runs the binary that it
# names and never the default toolchain (#7440). The second line of the output
# gives what each binary does under the caller's own environment: the line
# that names its hand-off, or `none`.
#
# A host bounds when its user manager runs scopes that enforce `MemoryMax`,
# and when it has `taskset`, GNU `/usr/bin/time`, `python3` and 2 cores.
# Elsewhere, as on macOS, the measure refuses and exits 2.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
# The secret of the key that the corpus site names. The driver's test of the
# two processes (#3374) proves the same key.
secret=0303030303030303030303030303030303030303030303030303030303030303
deployments=$root/corpus/model/deployments

# Why this host cannot bound a run, or nothing when it can.
refusal() {
  local held
  if ! command -v systemd-run > /dev/null; then
    echo "no systemd-run holds a scope"
    return
  fi
  # The probe reads the bound inside the scope, so its words expand there.
  # shellcheck disable=SC2016
  held=$(systemd-run --user --scope --quiet --collect -p MemoryMax=64M -p MemorySwapMax=0 -p OOMPolicy=continue \
    -- sh -c 'read -r line < /proc/self/cgroup; read -r max < "/sys/fs/cgroup${line#0::}/memory.max"; echo "$max"' 2> /dev/null) || held=
  if [[ $held != 67108864 ]]; then
    echo "no user scope holds a bound of memory"
    return
  fi
  local tool
  for tool in taskset python3; do
    command -v "$tool" > /dev/null || { echo "no $tool"; return; }
  done
  if ! /usr/bin/time -v true > /dev/null 2>&1; then
    echo "no GNU /usr/bin/time"
    return
  fi
  if (($(nproc) < 2)); then
    echo "fewer than 2 cores"
  fi
}

# Inside the scope: run `$@` on the first `$2` cores, under the wall-clock limit
# `$3`, and write the record of the run beside `$1`: its start, its first line
# and its end, its status, the kills that the scope saw and the peak that the
# scope charged.
inside() {
  local out=$1 cores=$2 limit=$3 line group start status
  shift 3
  read -r line < /proc/self/cgroup
  group=/sys/fs/cgroup${line#0::}
  start=$(date +%s.%N)
  set +e
  taskset -c "0-$((cores - 1))" /usr/bin/time -v -o "$out.time" timeout "$limit" "$@" 2>&1 \
    | while IFS= read -r line; do
      [[ -e $out.first ]] || date +%s.%N > "$out.first"
      printf '%s\n' "$line"
    done > "$out.output"
  status=${PIPESTATUS[0]}
  set -e
  date +%s.%N > "$out.end"
  echo "$start" > "$out.start"
  echo "$status" > "$out.status"
  awk '$1 == "oom_kill" { print $2 }' "$group/memory.events" > "$out.oom"
  if [[ -r $group/memory.peak ]]; then
    read -r line < "$group/memory.peak"
    echo "$line" > "$out.charged"
  fi
}

if [[ ${1:-} == --check-host ]]; then
  why=$(refusal)
  [[ -z $why ]] || { echo "small-device: this host cannot bound a run: $why (#7308)" >&2; exit 2; }
  exit 0
fi
if [[ ${1:-} == --inside ]]; then
  shift
  inside "$@"
  exit 0
fi

gandr=$(realpath "${1:?usage: small-device.bash <gandr> <counting> <sizes> [<limit>]}")
counting=$(realpath "${2:?usage: small-device.bash <gandr> <counting> <sizes> [<limit>]}")
sizes=$(realpath "${3:?usage: small-device.bash <gandr> <counting> <sizes> [<limit>]}")
limit=${4:-300}
why=$(refusal)
[[ -z $why ]] || { echo "small-device: this host cannot bound a run: $why (#7308)" >&2; exit 2; }
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
runs=0

# Run `$@` in a new scope under `$1` cores and `$2` of memory, its record at
# `$3`, over scratch directories of its own.
scoped() {
  local cores=$1 memory=$2 out=$3
  shift 3
  mkdir -p "$out.home/config" "$out.home/cache" "$out.home/data"
  GANDR_TOOLCHAIN_HANDOFF=never XDG_CONFIG_HOME=$out.home/config XDG_CACHE_HOME=$out.home/cache XDG_DATA_HOME=$out.home/data \
    systemd-run --user --scope --quiet --collect --unit "small-device-$$-${out##*.}" \
    -p MemoryMax="$memory" -p MemorySwapMax=0 -p OOMPolicy=continue \
    -- "$here/small-device.bash" --inside "$out" "$cores" "$limit" "$@" || true
}

# Print the row of the run recorded at `$5`: the path `$1`, which ends with the
# status `$2`, at `$3` cores and `$4` of memory, and `$6`, the issue that owes
# its end, or nothing. The host's refusal, when there is one, is the record's
# `refusal` file.
row() {
  local path=$1 ended=$2 cores=$3 memory=$4 out=$5 owed=${6:-}
  local status=137 oom=0 wall=0 first=null peak=0 charged=null allocation=
  [[ -e $out.status ]] && status=$(< "$out.status")
  [[ -s $out.oom ]] && oom=$(< "$out.oom")
  [[ -s $out.charged ]] && charged=$(< "$out.charged")
  [[ -e $out.refusal ]] || : > "$out.refusal"
  if [[ -e $out.start && -e $out.end ]]; then
    wall=$(awk -v start="$(< "$out.start")" -v end="$(< "$out.end")" 'BEGIN { printf "%.6f", end - start }')
    [[ -e $out.first ]] && first=$(awk -v start="$(< "$out.start")" -v first="$(< "$out.first")" 'BEGIN { printf "%.6f", first - start }')
  fi
  [[ -e $out.time ]] && peak=$(awk -F': ' '/Maximum resident set size/ { print $2 }' "$out.time")
  [[ -e $out.output ]] && allocation=$(awk 'match($0, /memory allocation of [0-9]+ bytes failed/) { split(substr($0, RSTART, RLENGTH), word, " "); print word[4] " bytes"; exit }' "$out.output")
  jq -n -c --arg path "$path" --argjson ended "$ended" --argjson cores "$cores" --arg memory "$memory" \
    --argjson status "$status" --argjson oom "$oom" --argjson wall "$wall" --argjson first "$first" \
    --argjson peak "${peak:-0}" --argjson charged "$charged" --arg allocation "$allocation" \
    --arg owed "$owed" --rawfile refused "$out.refusal" \
    '($refused | rtrimstr("\n")) as $refused
     | {path: $path, ended: $ended, cores: $cores, memory: $memory, status: $status, oom_kills: $oom,
        out_of_memory: ($allocation != ""), allocation: (if $allocation == "" then null else $allocation end),
        wall: $wall, first: $first, peak_kib: $peak, charged: $charged,
        refusal: (if $refused == "" then null else $refused end), owed: (if $owed == "" then null else $owed end)}' \
    | jq -r -L "$here" -f "$here/small-device.jq"
}

# One path at one bound: `$1` its name, `$2` the status it ends with, `$3`
# cores, `$4` memory, and the arguments of gandr.
measure() {
  local path=$1 ended=$2 cores=$3 memory=$4 out
  shift 4
  runs=$((runs + 1))
  out=$scratch/run.$runs
  (cd "$root" && scoped "$cores" "$memory" "$out" "$gandr" "$@")
  row "$path" "$ended" "$cores" "$memory" "$out"
}

# One check of the count build at `$2` cores, under the largest bound: `$1` its
# name, then the arguments of gandr. Its row gives the allocations and the
# frames that the check prints after its run.
counted() {
  local path=$1 cores=$2 out status=137 allocations=null frames=null line
  shift 2
  runs=$((runs + 1))
  out=$scratch/run.$runs
  (cd "$root" && scoped "$cores" 1G "$out" "$counting" "$@")
  [[ -e $out.status ]] && status=$(< "$out.status")
  [[ -e $out.output ]] && line=$(awk '/^counts: [0-9]+ allocations, [0-9]+ frames$/ { print $2, $4; exit }' "$out.output")
  [[ -n ${line:-} ]] && read -r allocations frames <<< "$line"
  jq -n -c --arg path "$path" --argjson cores "$cores" --argjson status "$status" \
    --argjson allocations "$allocations" --argjson frames "$frames" \
    '{path: $path, cores: $cores, status: $status, ended: 0, allocations: $allocations, frames: $frames}' \
    | jq -r -f "$here/small-device-counts.jq"
}

# The crossing at one bound: the bounded host of `far`, and the unbounded run
# that ships the migration to it once the host prints its peer.
crossing() {
  local cores=$1 memory=$2 out deploy port hosting
  runs=$((runs + 1))
  out=$scratch/run.$runs
  deploy=$scratch/deploy.$runs
  mkdir -p "$deploy" "$out.runner"
  port=$(python3 -c 'import socket; s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])')
  cp "$deployments/offers.gandr" "$deployments/offers.manifold.gandr" "$deploy/"
  awk -v port="$port" '{ gsub(/127\.0\.0\.1:7433/, "127.0.0.1:" port) } 1' "$deployments/offers.site.gandr" > "$deploy/offers.site.gandr"
  GANDR_SECRET_FAR=$secret scoped "$cores" "$memory" "$out" "$gandr" host --site "$deploy/offers.site.gandr" \
    --manifold "$deploy/offers.manifold.gandr" --migrations 1 "$deploy/offers.gandr" &
  hosting=$!
  until grep -q "@127.0.0.1:$port" "$out.output" 2> /dev/null; do
    kill -0 "$hosting" 2> /dev/null || break
    sleep 0.1
  done
  if kill -0 "$hosting" 2> /dev/null; then
    GANDR_TOOLCHAIN_HANDOFF=never XDG_CONFIG_HOME=$out.runner XDG_CACHE_HOME=$out.runner XDG_DATA_HOME=$out.runner \
      timeout "$limit" "$gandr" run --manifold "$deploy/offers.manifold.gandr" "$deploy/offers.gandr" > "$out.run" 2>&1 || true
  fi
  wait "$hosting" || true
  awk '/^refused a migration at / { sub(/^refused a migration at /, ""); print; exit }' "$out.output" > "$out.refusal" 2> /dev/null || true
  row "host far for offers.gandr" 0 "$cores" "$memory" "$out"
}

# What the binary `$1` does under the caller's own environment, with no
# switch: the line that names its hand-off, or `none` (#7440). The runs above
# refuse each hand-off, so this line tells a reader whether the binary, left
# alone, runs another build.
handoff() {
  local line
  line=$(cd "$root" && env -u GANDR_TOOLCHAIN_HANDOFF "$1" --version 2>&1 > /dev/null \
    | awk '/^gandr: .* hands off to / { print; exit }') || true
  echo "${line:-none}"
}

printf 'small-device: commit %s, %s, %s cores, gandr %s\n' \
  "$(git -C "$root" rev-parse HEAD)" "$(uname -m)" "$(nproc)" "$gandr"
printf 'small-device: hand-off of gandr: %s; of the count build: %s\n' "$(handoff "$gandr")" "$(handoff "$counting")"
echo "| Path | Cores | Allocations | Frames | Stop |"
echo "| --- | --- | --- | --- | --- |"
for cores in 1 2; do
  counted "check --recheck cost.gandr" "$cores" check --recheck --counts library/std/src/cost.gandr
done
for cores in 1 2; do
  counted "cold check functions.gandr" "$cores" check --counts crates/surface-corpus/strict/functions.gandr
done
echo
echo "| Frame | Variant | Bytes |"
echo "| --- | --- | --- |"
jq -R -s . "$sizes" | jq -r -f "$here/small-device-frames.jq"
echo
echo "| Path | Cores | Memory | Wall | First line | Peak | Charged | Stop |"
echo "| --- | --- | --- | --- | --- | --- | --- | --- |"
bounds=("1 64M" "1 256M" "1 1G" "2 64M" "2 256M" "2 1G")
for bound in "${bounds[@]}"; do
  read -r cores memory <<< "$bound"
  measure "run hello.gandr" 0 "$cores" "$memory" run corpus/model/effects/hello.gandr
done
for bound in "${bounds[@]}"; do
  read -r cores memory <<< "$bound"
  measure "check --recheck cost.gandr" 0 "$cores" "$memory" check --recheck library/std/src/cost.gandr
done
for bound in "${bounds[@]}"; do
  read -r cores memory <<< "$bound"
  measure "cold check functions.gandr" 0 "$cores" "$memory" check crates/surface-corpus/strict/functions.gandr
done
for bound in "${bounds[@]}"; do
  read -r cores memory <<< "$bound"
  crossing "$cores" "$memory"
done
awk '{ printf "load %s %s %s\n", $1, $2, $3 }' /proc/loadavg
