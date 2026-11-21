#!/usr/bin/env bash
# The landing's gate on another host of ours (#6996), run by `gate:remote`.
# A lane's gate runs on the host of its session, and a host that carries the
# cycle's runners or three seats that build is the slowest place for it. So
# the task runs the gate of the branch's head on the host with the least load
# for each core, and records the pass here.
#
# Usage: remote.bash [host]
#
# The hosts are the factory's configuration, never the tree's:
# `$XDG_CONFIG_HOME/gandr-factory/gate-hosts.json`, or the file `GANDR_GATE_HOSTS`
# names. It is `{"reader": <account>, "hosts": {<name>: {"ssh":
# [<argument>...], "checkout": <path>}}}`: the account whose token the far
# gate reads with, and for each host the argument vector that reaches it and
# the path of its checkout, relative to its home directory or absolute. An
# entry of the host that runs the task is skipped, since the task reads that
# host itself.
#
# The work must be HEAD on a branch. The far host gates a commit.
#
# The task reads the reader's token from this host's gh. It sends the token
# on the remote shell's standard input.
#
# Without a named host, each host gets `far.bash probe`. Each probe reports
# its load, cores and free gate slots. This host reports its own values. With
# no reader token here, each probe also checks its own token.
#
# `choose.jq` selects the host with the least load for each core. A failed
# probe gives no candidate. A selection of this host starts `mise run check`.
# Another selection pushes the head and starts `far.bash`.
#
# A passing far gate publishes its verdict records to `origin`. `passed.bash`
# admits its pass record here with the host's name. A failed or stopped gate
# records nothing and returns its status.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git rev-parse --show-toplevel)
config=${GANDR_GATE_HOSTS:-${XDG_CONFIG_HOME:-$HOME/.config}/gandr-factory/gate-hosts.json}
named=${1:-}

if [[ $("$here/passed.bash" tree) != "$(git rev-parse 'HEAD^{tree}')" ]]; then
  echo "gate:remote: the work holds changes that HEAD does not; commit them, then run gate:remote again" >&2
  exit 2
fi
if ! branch=$(git symbolic-ref --quiet --short HEAD); then
  echo "gate:remote: HEAD is on no branch; the far gate reads the claim of the branch's unit" >&2
  exit 2
fi
commit=$(git rev-parse HEAD)
[[ -r $config ]] || { echo "gate:remote: no host of ours is configured: $config is absent" >&2; exit 2; }
source "$here/../mise/gate.bash"
source "$here/../pr-stack/trunk.bash"
lane=$(gate_lane)
self=$(hostname -s)

# The argument vector that reaches host `$1`, one argument on each line.
ssh_of() {
  jq -r --arg host "$1" '.hosts[$host].ssh[]' "$config"
}

# Runs `far.bash` on host `$1` with the arguments after it. The source is a
# remote command so standard input stays a session pipe. The parent holds the
# pipe's writer until its local end stops. Its first line is the reader token.
# No argument vector, file or log holds that token.
handed=
far() {
  local host=$1 ssh=() word script command session status=0 ssh_pid
  shift
  while IFS= read -r word; do ssh+=("$word"); done < <(ssh_of "$host")
  script=$(< "$here/far.bash")
  printf -v command 'exec bash -c %q --' "$script"
  for word in "$@"; do printf -v command '%s %q' "$command" "$word"; done
  session=$(mktemp -d)
  mkfifo "$session/session"
  "${ssh[@]}" "bash -c $(printf '%q' "$command")" < "$session/session" &
  ssh_pid=$!
  exec 7> "$session/session"
  printf '%s\n' "$handed" >&7
  handed=
  wait "$ssh_pid" || status=$?
  exec 7>&-
  rm -rf "$session"
  return "$status"
}

host=$named
reader=$(jq -r '.reader // ""' "$config")
# The reader's token of this host's gh goes to the far gate, so a far host
# whose gh holds no such token still gates. With none here, each far gate
# takes the token from its own host's gh, and the probe reads which can.
token=
if [[ -n $reader ]]; then
  token=$(env -u GH_TOKEN -u GITHUB_TOKEN gh auth token --user "$reader" 2> /dev/null) || token=
fi
probe_reader=$reader
if [[ -n $token ]]; then probe_reader=; fi
if [[ -z $host ]]; then
  probes=$(mktemp -d)
  trap 'rm -rf "$probes"' EXIT
  bash "$here/far.bash" probe "$root" "$probe_reader" > "$probes/$self" 2> /dev/null &
  while IFS= read -r name; do
    far "$name" probe "$(jq -r --arg host "$name" '.hosts[$host].checkout' "$config")" "$probe_reader" > "$probes/$name" 2> /dev/null &
  done < <(jq -r --arg self "$self" '.hosts | keys[] | select(. != $self)' "$config")
  wait || :
  readings=$(for file in "$probes"/*; do
    if jq -e 'type == "object"' "$file" > /dev/null 2>&1; then
      jq -c --arg host "${file##*/}" '. + {host: $host}' "$file"
    else
      echo "gate:remote: ${file##*/} gave no probe, so it is passed over" >&2
    fi
  done | jq -sc .)
  jq -r '.[] | "gate:remote: \(.host): load \(.load) on \(.cores) cores, \(.free) free gate slots\(if .token == false then ", no token of the reader" else "" end)"' <<< "$readings" >&2
  host=$(jq -r -f "$here/choose.jq" <<< "$readings")
  if [[ $host == null ]]; then
    echo "gate:remote: no host of ours has a free gate slot and the reader's token; the gate waits for a slot here" >&2
    host=$self
  fi
fi

if [[ $host == "$self" ]]; then
  echo "gate:remote: $self runs the gate here" >&2
  exec mise run check
fi
jq -e --arg host "$host" '.hosts[$host].ssh | length > 0' "$config" > /dev/null \
  || { echo "gate:remote: $config names no host \`$host\`" >&2; exit 2; }
checkout=$(jq -r --arg host "$host" '.hosts[$host].checkout' "$config")
git push --quiet --force-with-lease -u origin HEAD
records=$(mktemp)
status=0
handed=$token
far "$host" gate "$checkout" "$(git remote get-url origin)" "$trunk" "$branch" "$commit" "$lane" "$reader" > "$records" || status=$?
handed=
if (( status != 0 )); then
  echo "gate:remote: the gate on $host failed or stopped, exit $status, so no pass is recorded" >&2
  rm -f "$records"
  exit "$status"
fi
"$here/passed.bash" admit "$host" "$commit" < "$records"
rm -f "$records"
