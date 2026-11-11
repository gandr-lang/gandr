# The host service that keeps a `mise` task running (#4167), sourced by each
# task with an `--install` and a `--remove`: `stall:watch` and
# `toolchain:follow`.
#
# `service_unit <install|remove> <name> <task> <description> [background]`
# installs or removes `service.jq`'s unit or agent: a `systemd --user` unit
# `gandr-<name>.service` under `$XDG_CONFIG_HOME/systemd/user/` on Linux, a
# `launchd` agent `gandr.<name>.plist` under `~/Library/LaunchAgents/` on
# macOS. With `background`, the service runs at the host's lowest priority
# (#6638). The service runs from this checkout at the commit it holds, so
# `--install` again restarts it at that tree's head. It runs under the
# installing shell's `PATH` and, where that shell sets them, the variables of
# `service_carried`, so git in the service reads the configuration the shell's
# git reads, never the host user's (#4866).

service_dir="$(git rev-parse --show-toplevel)/.config/service"

# The variables a service carries from the installing shell beside `PATH`:
# git's global configuration, and Cargo fetching git dependencies through git.
service_carried=(GIT_CONFIG_GLOBAL CARGO_NET_GIT_FETCH_WITH_CLI)

# launchd tears an agent down after `launchctl bootout` returns, and a
# bootstrap of its label before then fails `5: Input/output error` (#4875).
# An install waits until `launchctl print` no longer finds the label, polling
# `service_polls` times `service_pause` seconds apart: thirty seconds, past
# launchd's twenty-second exit timeout. It tries a bootstrap
# `service_bootstraps` times.
service_polls=60
service_pause=0.5
service_bootstraps=5

# `service_gone <target>` waits until launchd no longer holds `target`, and
# fails once the polls run out.
service_gone() {
  local target=$1 poll
  for (( poll = 0; poll < service_polls; poll++ )); do
    launchctl print "$target" > /dev/null 2>&1 || return 0
    sleep "$service_pause"
  done
  return 1
}

# `service_bootstrap <target> <file>` bootstraps the agent `file` states as
# `target`, waiting out a teardown before each try and pausing after a failed
# one, and fails once the tries run out.
service_bootstrap() {
  local target=$1 file=$2 try
  for (( try = 0; try < service_bootstraps; try++ )); do
    service_gone "$target" || return 1
    launchctl bootstrap "${target%/*}" "$file" && return 0
    sleep "$service_pause"
  done
  return 1
}

service_unit() {
  local action=$1 name=$2 task=$3 description=$4 background=false os file dir mise_bin environment target previous
  [[ ${5:-} != background ]] || background=true
  case "$(uname -s)" in
    Linux) os=linux file="${XDG_CONFIG_HOME:-$HOME/.config}/systemd/user/gandr-$name.service" ;;
    Darwin) os=macos file="$HOME/Library/LaunchAgents/gandr.$name.plist" target="gui/$(id -u)/gandr.$name" ;;
    *) echo "$task --$action knows Linux and macOS, not $(uname -s)" >&2; return 2 ;;
  esac
  if [[ "$os" == linux ]]; then
    systemctl --user disable --now "gandr-$name.service" 2> /dev/null || :
  else
    launchctl bootout "$target" 2> /dev/null || :
    service_gone "$target" || { echo "$task --$action: launchd still holds $target after its bootout" >&2; return 1; }
  fi
  if [[ "$action" == remove ]]; then
    rm -f "$file"
    if [[ "$os" == linux ]]; then systemctl --user daemon-reload; fi
    echo "$task: the service is removed ($file)" >&2
    return 0
  fi
  mise_bin=$(command -v mise) || { echo "$task --install needs mise on PATH" >&2; return 2; }
  dir=$(git rev-parse --show-toplevel)
  mkdir -p "$(dirname "$file")"
  previous=$( [[ -f "$file" ]] && cat "$file" ) || previous=
  environment=$(for variable in "${service_carried[@]}"; do
    [[ -z ${!variable:-} ]] || jq -n --arg key "$variable" --arg value "${!variable}" '{($key): $value}'
  done | jq -s 'add // {}')
  jq -rn --arg os "$os" --arg dir "$dir" --arg mise "$mise_bin" --arg path "$PATH" --argjson environment "$environment" \
    --arg name "$name" --arg task "$task" --arg description "$description" --argjson background "$background" \
    '{os: $os, dir: $dir, mise: $mise, path: $path, environment: $environment, name: $name, task: $task, description: $description, background: $background}' \
    | jq -r -f "$service_dir/service.jq" > "$file"
  if [[ "$os" == linux ]]; then
    systemctl --user daemon-reload
    systemctl --user enable --now "gandr-$name.service"
  elif ! service_bootstrap "$target" "$file"; then
    if [[ -n "$previous" ]] && printf '%s\n' "$previous" > "$file" && service_bootstrap "$target" "$file"; then
      echo "$task --install: launchd refused the new agent $target, and the previous one is loaded again" >&2
    else
      echo "$task --install: launchd refused the agent $target, and no agent is loaded" >&2
    fi
    return 1
  fi
  echo "$task: the service runs from $dir ($file)" >&2
}
