# The toolchain follower (#4499), sourced by `toolchain:follow`. Each reading
# fetches `origin main` into the main checkout, fast-forwards it, builds the
# driver there and deploys the build as the default toolchain, so every relay
# and every `gandr` the proxy runs follows `main`. It then syncs the
# checkout's code index and warms the builds a gate and `pr:open` make, which
# every new worktree copies (#4866, `follow_warm`). On the builder, each
# fast-forward also pushes the host tools to the hosts that receive them
# (#7008, `follow_tools`).
#
# No seat and no editor reloads for new tooling. A running `gandr lsp` or
# `gandr mcp` moves to the deployed build in place, on the next request its
# client sends, and keeps its process and its session (`followed` in
# `crates/surface-driver/src/main.rs`). A relay that sends nothing stays on
# its build until it sends.
#
# Each build, each warm build and each push runs in the environment of the
# commit that the checkout holds, under the channel that it pins
# (`toolchain/tree.bash`, #7486). The service starts once, and mise sets its
# `RUSTUP_TOOLCHAIN` from the pin of the checkout at that start. So without
# it, a main that moves the pin builds under the pin before it. The loop of
# `toolchain:follow` sources this file once, so a change of this file
# reaches a running service only when the service starts again.
#
# The configuration and the follower's memory live outside the tree, under
# the XDG directories:
#   $XDG_CONFIG_HOME/gandr/follow.json   `{checkout, interval, page}`: the
#       main checkout it builds in, the seconds between readings, and the
#       page command's argument vector before the line;
#   $XDG_CONFIG_HOME/gandr/host-tools.toml   the builder's configuration,
#       on the builder only (`crates/workflow-host-tools`);
#   $XDG_STATE_HOME/gandr/follow.json    `{deployed, previous, failed,
#       fetch_failures, indexed, warmed, pushed, paged}`: the commit
#       deployed, the one deployed before it, the last commit whose build
#       cargo refused, the failed fetches in a row, the commits the code
#       index was last synced to, the gates' builds last warmed at and the
#       host tools last pushed at, and the keys of the pages already sent;
#   $XDG_STATE_HOME/gandr/follow-build.log   the output of the last build;
#   $XDG_STATE_HOME/gandr/follow-tools.log   the output of the last push.
# The builds live in `$XDG_DATA_HOME/gandr/builds/<commit>/gandr`. The
# toolchain `main` names the deployed build and is the default, and the
# toolchain `previous` names the build before it, for a rollback by
# `gandr toolchain default previous`.
#
# A main checkout older than the follower has no `toolchain:follow`. Before
# the first `--install`, fast-forward it once to `origin/main`.

follow_dir="$(git rev-parse --show-toplevel)/.config/follow"
source "$follow_dir/../toolchain/tree.bash"
follow_config="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/follow.json"
follow_state="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/follow.json"
follow_build_log="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/follow-build.log"
follow_host_tools="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/host-tools.toml"
follow_tools_log="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/follow-tools.log"
follow_builds="${XDG_DATA_HOME:-$HOME/.local/share}/gandr/builds"
follow_toolchains="${XDG_DATA_HOME:-$HOME/.local/share}/gandr/toolchains"
# The page command's argument vector before the line, the configuration's
# `page`, set by `toolchain:follow`.
follow_page_command=()

# The configuration, or nothing on stdout and exit 2 when it is missing or
# malformed.
follow_configuration() {
  if [[ -f "$follow_config" ]] && jq -e '(.checkout | type == "string")
      and (.interval | type == "number" and . > 0)
      and (.page | type == "array" and length > 0 and all(type == "string"))' "$follow_config" > /dev/null; then
    jq -c . "$follow_config"
    return
  fi
  echo "toolchain:follow reads $follow_config: {\"checkout\": <the main checkout>, \"interval\": <seconds>, \"page\": [<page script>, <its arguments before the line>, ...]}" >&2
  return 2
}

# The memory the last reading left, `{}` when there is none.
follow_memory() {
  if [[ -f "$follow_state" ]]; then jq -c . "$follow_state"; else echo '{}'; fi
}

# Write the memory `$1`.
follow_remember() {
  mkdir -p "$(dirname "$follow_state")"
  jq -c . <<< "$1" > "$follow_state.tmp"
  mv "$follow_state.tmp" "$follow_state"
}

# Page the line `$2` once under the key `$1`: a key already paged sends
# nothing. A page that fails is sent again at the next reading. The memory
# keeps the last 32 keys.
follow_page() {
  local key=$1 line=$2 memory
  memory=$(follow_memory)
  echo "$line"
  if jq -e --arg key "$key" '(.paged // []) | index($key)' <<< "$memory" > /dev/null; then return 0; fi
  "${follow_page_command[@]}" "$line" || return 0
  follow_remember "$(jq -c --arg key "$key" '.paged = ((.paged // []) + [$key])[-32:]' <<< "$memory")"
}

# Whether a process runs the executable `$1`.
follow_live() {
  local exe
  if command -v lsof > /dev/null; then
    lsof -t -- "$1" > /dev/null 2>&1
    return
  fi
  for exe in /proc/[0-9]*/exe; do
    [[ $(readlink "$exe" 2> /dev/null) == "$1" ]] && return 0
  done
  return 1
}

# Deploy the build of commit `$1` from the checkout's `target/release`: copy
# it under its commit, link it as `main` and the build before it as
# `previous`, make `main` the default, then remove every other build no
# process runs (`prune.jq`).
follow_deploy() {
  local head=$1 memory previous dir builds live build canonical link
  memory=$(follow_memory)
  previous=$(jq -r '.deployed // empty' <<< "$memory")
  dir="$follow_builds/$head"
  mkdir -p "$dir"
  cp target/release/gandr "$dir/gandr.part"
  mv "$dir/gandr.part" "$dir/gandr"
  "$dir/gandr" toolchain link main "$dir" > /dev/null
  if [[ -n "$previous" && "$previous" != "$head" && -x "$follow_builds/$previous/gandr" ]]; then
    "$dir/gandr" toolchain link previous "$follow_builds/$previous" > /dev/null
  else
    previous=
  fi
  "$dir/gandr" toolchain default main > /dev/null
  follow_remember "$(jq -c --arg head "$head" --arg previous "$previous" \
    '.deployed = $head | .previous = (if $previous == "" then null else $previous end)' <<< "$memory")"
  builds='[]'
  live='[]'
  for build in "$follow_builds"/*/; do
    build=${build%/}
    build=${build##*/}
    builds=$(jq -c --arg b "$build" '. + [$b]' <<< "$builds")
    if follow_live "$follow_builds/$build/gandr"; then live=$(jq -c --arg b "$build" '. + [$b]' <<< "$live"); fi
  done
  canonical=$(cd "$follow_builds" && pwd -P)
  for build in $(jq -n -r --argjson builds "$builds" --arg current "$head" --arg previous "$previous" --argjson live "$live" \
      '{builds: $builds, current: $current, previous: (if $previous == "" then null else $previous end), live: $live}' \
      | jq -r -f "$follow_dir/prune.jq" | jq -r '.[]'); do
    rm -rf "${follow_builds:?}/$build"
    # A toolchain linked to the removed build goes with it.
    for link in "$follow_toolchains"/*; do
      if [[ -f "$link" && $(head -n 1 "$link") == "$canonical/$build" ]]; then rm -f "$link"; fi
    done
    echo "toolchain:follow: removed the build of $build"
  done
  echo "toolchain:follow: deployed $head as the default toolchain main${previous:+, $previous as previous}"
}

# Bring the main checkout's code index to `HEAD` `$1` where one exists
# (#4866): `wt:warm` copies it into every new worktree, which then starts with
# the index of the `main` it branched from. An index already at `$1` is left
# alone. A failed sync is printed and paged once per commit, read again next
# interval, and never holds back a deploy.
follow_index() {
  local head=$1 output
  [[ -d .codegraph ]] || return 0
  [[ "$head" != $(jq -r '.indexed // empty' <<< "$(follow_memory)") ]] || return 0
  if ! output=$(mise exec -- codegraph sync 2>&1); then
    echo "$output" >&2
    follow_page "index:$head" "FOLLOW index-failed: the code index of $PWD does not sync to ${head:0:9}: $(awk 'NF {line = $0} END {print line}' <<< "$output")"
    return 0
  fi
  follow_remember "$(jq -c --arg head "$head" '.indexed = $head' <<< "$(follow_memory)")"
  echo "toolchain:follow: synced the code index to $head"
}

# Build at `HEAD` `$1`, in the main checkout, what a gate and `pr:open` build:
# the plain and enforcing test targets, both Clippy walls, the Dylint wall,
# the rustdoc evidence and the workflow tools. `wt:warm` copies the
# checkout's `target/` into every new worktree; the release build alone left
# those cold, so each worktree's first gate built them whole. The builds run
# in the background, one at a time, at the lowest CPU priority and outside
# every gate slot (`GANDR_GATE_SLOT`), so no reading or deploy waits on them.
# A reading that finds them running leaves its head to the reading after
# they end; a lock whose builder has exited is taken again. A failed step is
# printed and the next one runs: the warm state is a cache, never a verdict.
follow_warm() {
  local head=$1 lock="$follow_state.warming" builder
  [[ "$head" != $(jq -r '.warmed // empty' <<< "$(follow_memory)") ]] || return 0
  mkdir -p "$(dirname "$follow_state")"
  if ! mkdir "$lock" 2> /dev/null; then
    builder=$(< "$lock/pid") 2> /dev/null || builder=
    if [[ -n $builder ]] && kill -0 "$builder" 2> /dev/null; then return 0; fi
    rm -rf -- "$lock"
    mkdir "$lock" 2> /dev/null || return 0
  fi
  (
    trap 'rm -rf -- "$lock"' EXIT
    echo "$BASHPID" > "$lock/pid"
    export GANDR_GATE_SLOT=follow
    echo "toolchain:follow: warming the gates' builds at ${head:0:9}"
    for task in build:tests build:tests-enforcing check:clippy check:clippy-enforcing check:dylint evidence:rustdoc workflow:install; do
      tree_exec "$PWD" nice -n 19 mise run --quiet "$task" > /dev/null 2>&1 || echo "toolchain:follow: warming $task at ${head:0:9} failed"
    done
    follow_remember "$(jq -c --arg head "$head" '.warmed = $head' <<< "$(follow_memory)")"
    echo "toolchain:follow: warmed the gates' builds at ${head:0:9}"
  ) &
}

# Run `tools:push` at `HEAD` `$1` on the builder (#7008): the host whose
# configuration `host-tools.toml` stands. The push builds the keys of each
# receiver's target, copies each key to its receivers and brings mise to the
# pin on each host; a host with no receiver gets nothing. Like `follow_warm`,
# it runs in the background, at the lowest CPU priority and outside every
# gate slot, so no build or deploy waits on it. A reading that finds it
# running leaves its head to the reading after it ends. A failed push is
# paged once per commit and runs again at the next reading; its markers keep
# each copy that ended, so the next push copies only the rest.
follow_tools() {
  local head=$1 lock="$follow_state.pushing" pusher
  [[ -f "$follow_host_tools" ]] || return 0
  [[ "$head" != $(jq -r '.pushed // empty' <<< "$(follow_memory)") ]] || return 0
  mkdir -p "$(dirname "$follow_state")"
  if ! mkdir "$lock" 2> /dev/null; then
    pusher=$(< "$lock/pid") 2> /dev/null || pusher=
    if [[ -n $pusher ]] && kill -0 "$pusher" 2> /dev/null; then return 0; fi
    rm -rf -- "$lock"
    mkdir "$lock" 2> /dev/null || return 0
  fi
  (
    trap 'rm -rf -- "$lock"' EXIT
    echo "$BASHPID" > "$lock/pid"
    export GANDR_GATE_SLOT=follow
    echo "toolchain:follow: pushing the host tools at ${head:0:9}"
    if tree_exec "$PWD" nice -n 19 mise run --quiet tools:push > "$follow_tools_log" 2>&1; then
      follow_remember "$(jq -c --arg head "$head" '.pushed = $head' <<< "$(follow_memory)")"
      echo "toolchain:follow: pushed the host tools at ${head:0:9}"
    else
      follow_page "tools:$head" "FOLLOW tools-failed: tools:push at ${head:0:9} failed: $(awk '/^failed/ {line = $0} END {print line}' "$follow_tools_log")"
    fi
  ) &
}

# One reading in the checkout `$1`: fetch, fast-forward, push the host tools
# on the builder, build, deploy, sync the code index and warm the gates'
# builds. A checkout off `main`, dirty, or past `origin/main` is left as it
# is and paged once per commit of `origin/main`. A fetch that fails twice in
# a row is paged once per commit of `origin/main` last fetched (#4866). A
# build that cargo refuses deploys nothing and is paged once per commit. A
# build that a signal ends records nothing, and the next reading builds the
# commit again.
follow_once() {
  local checkout=$1 upstream branch head memory error url prefix status failures index
  cd "$checkout" || { follow_page "missing:$checkout" "FOLLOW checkout-missing: $checkout is no directory; nothing deployed"; return; }
  # The user's git configuration can rewrite origin's URL, as an `insteadOf`
  # that sends it to ssh where the service holds no key. A map of origin's
  # owner prefix onto itself is longer than such a rewrite, so it wins. The
  # fetch and cargo's fetches of the owner's git dependencies read it from
  # the environment.
  if url=$(git config --get remote.origin.url); then
    prefix=${url%/*}/
    index=${GIT_CONFIG_COUNT:-0}
    export "GIT_CONFIG_KEY_$index=url.$prefix.insteadOf" "GIT_CONFIG_VALUE_$index=$prefix" GIT_CONFIG_COUNT=$((index + 1))
  fi
  if ! error=$(git fetch -q origin main 2>&1); then
    echo "$error" >&2
    upstream=$(git rev-parse -q --verify origin/main || echo none)
    memory=$(follow_memory)
    failures=$(( $(jq '.fetch_failures // 0' <<< "$memory") + 1 ))
    follow_remember "$(jq -c --argjson failures "$failures" '.fetch_failures = $failures' <<< "$memory")"
    # One failed fetch can be a moment of the network: the second in a row pages.
    if (( failures >= 2 )); then
      follow_page "fetch:$upstream" "FOLLOW fetch-failed: $checkout cannot fetch origin main, $failures times in a row: $(awk 'NF {print; exit}' <<< "$error"); nothing past ${upstream:0:9} is deployed"
    fi
    return
  fi
  memory=$(follow_memory)
  if jq -e 'has("fetch_failures")' <<< "$memory" > /dev/null; then
    follow_remember "$(jq -c 'del(.fetch_failures)' <<< "$memory")"
  fi
  upstream=$(git rev-parse origin/main)
  branch=$(git symbolic-ref -q --short HEAD || echo detached)
  if [[ "$branch" != main ]]; then
    follow_page "off-main:$upstream" "FOLLOW off-main: $checkout is on $branch, not main; ${upstream:0:9} is not deployed"
    return
  fi
  if [[ -n $(git status --porcelain --untracked-files=no) ]]; then
    follow_page "dirty:$upstream" "FOLLOW dirty: $checkout has uncommitted changes; ${upstream:0:9} is not deployed"
    return
  fi
  if ! git merge -q --ff-only origin/main; then
    follow_page "diverged:$upstream" "FOLLOW diverged: $checkout cannot fast-forward to ${upstream:0:9}; nothing deployed"
    return
  fi
  head=$(git rev-parse HEAD)
  follow_tools "$head"
  memory=$(follow_memory)
  if [[ "$head" != $(jq -r '.deployed // empty' <<< "$memory") && "$head" != $(jq -r '.failed // empty' <<< "$memory") ]]; then
    echo "toolchain:follow: building $head"
    # The build writes to its log, so an output pipe that closes cannot end it.
    mkdir -p "$(dirname "$follow_build_log")"
    status=0
    tree_exec "$PWD" cargo build --release --locked -p gandr-lang --bin gandr > "$follow_build_log" 2>&1 || status=$?
    if (( status == 0 )); then
      follow_deploy "$head"
    elif (( status > 128 )); then
      echo "toolchain:follow: signal $((status - 128)) ended the build of $head; the next reading builds it again" >&2
    else
      follow_remember "$(jq -c --arg head "$head" '.failed = $head' <<< "$(follow_memory)")"
      follow_page "build:$head" "FOLLOW build-failed: main at ${head:0:9} does not build: $(awk '/^error/ {line = $0} END {print line}' "$follow_build_log"); the default stays $(jq -r '.deployed // "unchanged"' <<< "$memory" | cut -c1-9)"
    fi
  fi
  follow_index "$head"
  follow_warm "$head"
}
