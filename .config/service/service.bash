# The host service that keeps a `mise` task running (#4167), sourced by each
# task with an `--install` and a `--remove`: `stall:watch` and
# `toolchain:follow`.
#
# `service_unit <install|remove> <name> <task> <description>` installs or
# removes `service.jq`'s unit or agent: a `systemd --user` unit
# `gandr-<name>.service` under `$XDG_CONFIG_HOME/systemd/user/` on Linux, a
# `launchd` agent `gandr.<name>.plist` under `~/Library/LaunchAgents/` on
# macOS. The service runs from this checkout at the commit it holds, so
# `--install` again restarts it at that tree's head.

service_dir="$(git rev-parse --show-toplevel)/.config/service"

service_unit() {
  local action=$1 name=$2 task=$3 description=$4 os file dir mise_bin
  case "$(uname -s)" in
    Linux) os=linux file="${XDG_CONFIG_HOME:-$HOME/.config}/systemd/user/gandr-$name.service" ;;
    Darwin) os=macos file="$HOME/Library/LaunchAgents/gandr.$name.plist" ;;
    *) echo "$task --$action knows Linux and macOS, not $(uname -s)" >&2; return 2 ;;
  esac
  if [[ "$os" == linux ]]; then
    systemctl --user disable --now "gandr-$name.service" 2> /dev/null || :
  else
    launchctl bootout "gui/$(id -u)/gandr.$name" 2> /dev/null || :
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
  jq -rn --arg os "$os" --arg dir "$dir" --arg mise "$mise_bin" --arg path "$PATH" \
    --arg name "$name" --arg task "$task" --arg description "$description" \
    '{os: $os, dir: $dir, mise: $mise, path: $path, name: $name, task: $task, description: $description}' \
    | jq -r -f "$service_dir/service.jq" > "$file"
  if [[ "$os" == linux ]]; then
    systemctl --user daemon-reload
    systemctl --user enable --now "gandr-$name.service"
  else
    launchctl bootstrap "gui/$(id -u)" "$file"
  fi
  echo "$task: the service runs from $dir ($file)" >&2
}
