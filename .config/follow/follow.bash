# The toolchain follower (#4499), sourced by `toolchain:follow`. Each reading
# fetches `origin main` into the main checkout, fast-forwards it, builds the
# driver there and deploys the build as the default toolchain, so every relay
# and every `gandr` the proxy runs follows `main`.
#
# The configuration and the follower's memory live outside the tree, under
# the XDG directories:
#   $XDG_CONFIG_HOME/gandr/follow.json   `{checkout, interval, page}`: the
#       main checkout it builds in, the seconds between readings, and the
#       page command's argument vector before the line;
#   $XDG_STATE_HOME/gandr/follow.json    `{deployed, previous, failed, paged}`:
#       the commit deployed, the one deployed before it, the last commit whose
#       build failed, and the keys of the pages already sent.
# The builds live in `$XDG_DATA_HOME/gandr/builds/<commit>/gandr`. The
# toolchain `main` names the deployed build and is the default, and the
# toolchain `previous` names the build before it, for a rollback by
# `gandr toolchain default previous`.

follow_dir="$(git rev-parse --show-toplevel)/.config/follow"
follow_config="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/follow.json"
follow_state="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/follow.json"
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

# One reading in the checkout `$1`: fetch, fast-forward, build and deploy.
# A checkout off `main`, dirty, or past `origin/main` is left as it is and
# paged once per commit of `origin/main`. A failed build deploys nothing and
# is paged once per commit.
follow_once() {
  local checkout=$1 upstream branch head memory
  cd "$checkout" || { follow_page "missing:$checkout" "FOLLOW checkout-missing: $checkout is no directory; nothing deployed"; return; }
  if ! git fetch -q origin main; then
    echo "toolchain:follow: the fetch failed; reading again next interval" >&2
    return
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
  memory=$(follow_memory)
  if [[ "$head" == $(jq -r '.deployed // empty' <<< "$memory") || "$head" == $(jq -r '.failed // empty' <<< "$memory") ]]; then
    return
  fi
  echo "toolchain:follow: building $head"
  if ! cargo build --release --locked -p gandr-lang --bin gandr; then
    follow_remember "$(jq -c --arg head "$head" '.failed = $head' <<< "$(follow_memory)")"
    follow_page "build:$head" "FOLLOW build-failed: main at ${head:0:9} does not build; the default stays $(jq -r '.deployed // "unchanged"' <<< "$memory" | cut -c1-9)"
    return
  fi
  follow_deploy "$head"
}
