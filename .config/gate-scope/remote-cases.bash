#!/usr/bin/env bash
# A remote gate runs in `check:gate-scope`.
# - see: #6996, `remote.bash`, `far.bash`
#
# A fake `ssh` starts the far side on this host. Each fake host gets a home
# directory. A fake `mise` executes the far gate.
#
# The fake gate writes the pass record and verdict reference. A bare scratch
# repository serves as `origin`. The test setup links `.config` into each
# scratch tree. The cases inspect the returned record, refusals and free slots.
# The `choose.jq` cases in `cases.json` select the host.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
config_dir=$(cd "$here/.." && pwd)
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
pids=()
far_groups=()
cleanup() {
  local pid group
  for pid in ${pids[@]+"${pids[@]}"}; do kill -KILL "$pid" 2> /dev/null || true; done
  for group in ${far_groups[@]+"${far_groups[@]}"}; do kill -KILL -- "-$group" 2> /dev/null || true; done
  rm -rf "$scratch"
}
trap cleanup EXIT
failed=0

fail() {
  echo "remote case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# The first argument of the stand-in `ssh` is the host.
# It runs the far command in a session of its own.
# It gives that session a separate home, state directory and path.
# An ssh session carries no `GH_TOKEN` of this host.
# It writes its arguments to `ssh-args`.
mkdir -p "$scratch/bin" "$scratch/far-bin" "$scratch/near-bin"
cat > "$scratch/bin/ssh" << EOF
#!/usr/bin/env bash
printf '%s\n' "\$*" >> $scratch/ssh-args
host=\$1
shift
unset GH_TOKEN
export HOME=$scratch/home-\$host XDG_STATE_HOME=$scratch/home-\$host/state PATH=$scratch/far-bin:\$PATH
mkdir -p "\$HOME"
if [[ \${GANDR_REMOTE_SESSION_CASE:-} == 1 ]]; then
  trap '' TERM HUP
  perl -MPOSIX=setsid -e 'setsid() or die "setsid\n"; \$SIG{TERM} = "DEFAULT"; \$SIG{HUP} = "DEFAULT"; exec @ARGV' bash -c "\$*" <&0 &
  child=\$!
  printf '%s\n' "\$child" > "\$HOME/session-group"
  wait "\$child"
  exit \$?
fi
exec perl -MPOSIX=setsid -e 'setsid() or die "setsid\n"; exec @ARGV' bash -c "\$*"
EOF
# The stand-in `gh` of this host gives the token in `near-token` for the
# account `reader`, and none when the file is absent.
cat > "$scratch/near-bin/gh" << EOF
#!/usr/bin/env bash
[[ "\$*" == 'auth token --user reader' && -e $scratch/near-token ]] || exit 1
cat $scratch/near-token
EOF
# The stand-in `gh` of the far host gives the token of the account `reader`
# alone.
cat > "$scratch/far-bin/gh" << 'EOF'
#!/usr/bin/env bash
[[ "$*" == 'auth token --user reader' ]] || exit 1
echo read-token
EOF
# The far host's fake `mise` handles three command calls. `trust` exits zero.
# `run tools:check` reads the host's tools. It emits status 2 when the host
# home holds `lacks`.
#
# `run check` touches `gated`. It writes the pass record and the tree's
# verdict reference. It rejects a red gate or a gate without the reader's
# token. It writes the token to the host's `token` file.
cat > "$scratch/far-bin/mise" << 'EOF'
#!/usr/bin/env bash
case "${1:-} ${2:-}" in
  trust\ *) exit 0 ;;
  'run tools:check')
    if [[ -e $HOME/lacks ]]; then echo 'host-tools: far lacks github:cli/cli 2.103.2' >&2; exit 2; fi
    echo 'host-tools: far holds each tool'
    ;;
  'run check')
    touch "$HOME/gated"
    if [[ -e $HOME/hold ]]; then
      : > "$HOME/held"
      until [[ -e $HOME/release ]]; do sleep 0.1; done
    fi
    if [[ -e $HOME/red ]]; then echo 'check: a check is red' >&2; exit 1; fi
    case ${GH_TOKEN:-} in
      read-token | handed-token) printf '%s\n' "$GH_TOKEN" > "$HOME/token" ;;
      *) echo "check: the gate reads with \`${GH_TOKEN:-}\`, not the reader's token" >&2; exit 1 ;;
    esac
    tree=$(git rev-parse 'HEAD^{tree}')
    dir=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-gate/$tree
    mkdir -p "$dir"
    printf '{"tree": "%s", "commit": "%s", "gate": "check", "checks": ["check:gate-scope"], "tasks": ["check:gate-scope"], "at": "%s"}\n' \
      "$tree" "$(git rev-parse HEAD)" "$(date -u +%FT%TZ)" > "$dir/a.json"
    git update-ref "refs/verdicts/$tree/check-gate-scope/case" "$(git rev-parse HEAD)"
    echo 'check: every check passes'
    ;;
  *) exit 2 ;;
esac
EOF
chmod +x "$scratch/bin/ssh" "$scratch/near-bin/gh" "$scratch/far-bin/gh" "$scratch/far-bin/mise"
export PATH=$scratch/near-bin:$PATH

# `origin`, with `landing` at a base that links `.config`; the far host's
# checkout, a clone of it; and this host's work, a clone on the branch
# `flex-a-6996-case`.
git init --quiet --bare -b landing "$scratch/origin.git"
git clone --quiet "$scratch/origin.git" "$scratch/seed" 2> /dev/null
(
  cd "$scratch/seed"
  identity
  git symbolic-ref HEAD refs/heads/landing
  ln -s "$config_dir" .config
  printf 'base\n' > file
  git add -A && git commit --quiet -m base
  git push --quiet origin landing
)
git clone --quiet "$scratch/origin.git" "$scratch/far-checkout"
git clone --quiet "$scratch/origin.git" "$scratch/work"
cd "$scratch/work"
identity
git checkout --quiet -b flex-a-6996-case
commit file own own
printf '{"reader": "reader", "hosts": {"far": {"ssh": ["%s", "far"], "checkout": "%s"}}}\n' "$scratch/bin/ssh" "$scratch/far-checkout" > "$scratch/hosts.json"
export GANDR_GATE_HOSTS=$scratch/hosts.json
export GANDR_HOST_LOCK_DIR=$scratch/locks
records=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-gate

# With no token of the reader here, a far gate that passes reads with the
# far host's reader's token. It gives its record, which lands here under the
# head's tree, with the host's name.
status=0
"$here/remote.bash" far > "$scratch/out" 2>&1 || status=$?
tree=$(git rev-parse 'HEAD^{tree}')
got=$(jq -sc '[.[] | {commit, host}]' "$records/$tree"/*.json 2> /dev/null || echo none)
[[ $status == 0 && $got == "[{\"commit\":\"$(git rev-parse HEAD)\",\"host\":\"far\"}]" && $(< "$scratch/home-far/token") == read-token ]] \
  || fail "#6996: a far gate that passes with its host's reader's token records its pass here under the head's tree, with its host" "exit $status, $got: $(< "$scratch/out")"
[[ $(git rev-parse origin/flex-a-6996-case) == "$(git rev-parse HEAD)" ]] \
  || fail "#6996: the task pushes the head to origin before the far gate" "$(git rev-parse origin/flex-a-6996-case 2>&1)"
remote_ref=$(git --git-dir="$scratch/origin.git" for-each-ref --count=1 "refs/verdicts/$tree/")
[[ -n $remote_ref ]] \
  || fail "#8166: a far gate publishes the verdict record of a pushed head without pr:open" "$remote_ref"

# This host's reader's token goes to the far gate on the remote shell's
# standard input. No argument vector of ssh and no line of the task holds it.
printf 'handed-token\n' > "$scratch/near-token"
commit file handed handed
status=0
"$here/remote.bash" far > "$scratch/out" 2>&1 || status=$?
tree=$(git rev-parse 'HEAD^{tree}')
got=$(jq -sc '[.[] | {commit, host}]' "$records/$tree"/*.json 2> /dev/null || echo none)
[[ $status == 0 && $got == "[{\"commit\":\"$(git rev-parse HEAD)\",\"host\":\"far\"}]" && $(< "$scratch/home-far/token") == handed-token ]] \
  || fail "#6996: a far gate reads with the reader's token of the calling host" "exit $status, $got, token $(< "$scratch/home-far/token"): $(< "$scratch/out")"
if [[ $(< "$scratch/ssh-args") == *handed-token* || $(< "$scratch/out") == *handed-token* ]]; then
  fail "#6996: the handed token is in no argument vector and no line" "$(< "$scratch/ssh-args")"
fi
rm "$scratch/near-token"

# A far gate that fails records nothing, and the task gives its status.
touch "$scratch/home-far/red"
commit file red red
status=0
"$here/remote.bash" far > "$scratch/out" 2>&1 || status=$?
tree=$(git rev-parse 'HEAD^{tree}')
[[ $status == 1 && ! -e $records/$tree ]] \
  || fail "#6996: a far gate that fails records no pass" "exit $status, records: $(ls "$records/$tree" 2>&1)"
rm "$scratch/home-far/red"

# A far host that lacks a tool stops before its gate (#7127): the gate does
# not run, nothing is recorded, the task gives the check's status 2, and the
# lack stands in its lines.
touch "$scratch/home-far/lacks"
rm -f "$scratch/home-far/gated"
commit file lacks lacks
status=0
"$here/remote.bash" far > "$scratch/out" 2>&1 || status=$?
tree=$(git rev-parse 'HEAD^{tree}')
[[ $status == 2 && ! -e $records/$tree && ! -e $scratch/home-far/gated && $(< "$scratch/out") == *'far lacks github:cli/cli 2.103.2'* ]] \
  || fail "#7127: a far host that lacks a tool stops before its gate and records no pass" "exit $status, gated $([[ -e $scratch/home-far/gated ]] && echo yes || echo no): $(< "$scratch/out")"
rm "$scratch/home-far/lacks"

# A second far gate waits before it moves the shared lane clone. The first
# check holds at its first tree until the test releases it.
far_gate() {
  local commit=$1 session child status=0
  session=$(mktemp -d)
  mkfifo "$session/session"
  env GH_TOKEN=read-token HOME="$scratch/home-far" XDG_STATE_HOME="$scratch/home-far/state" \
    PATH="$scratch/far-bin:$PATH" bash "$here/far.bash" gate "$scratch/far-checkout" \
    "$scratch/origin.git" landing flex-a-6996-case "$commit" flex-a < "$session/session" &
  child=$!
  exec 7> "$session/session"
  printf '\n' >&7
  wait "$child" || status=$?
  exec 7>&-
  rm -rf "$session"
  return "$status"
}
touch "$scratch/home-far/hold"
commit file lane-first lane-first
git push --quiet origin HEAD
first=$(git rev-parse HEAD)
far_gate "$first" > "$scratch/first-gate.out" 2>&1 &
first_gate=$!
pids+=("$first_gate")
tries=0
until [[ -e $scratch/home-far/held ]]; do
  (( ++tries < 100 )) || { fail "#7758: the first far gate never reached its check" "$(< "$scratch/first-gate.out")"; break; }
  sleep 0.1
done
clone=$scratch/home-far/state/gandr/gate-remote/flex-a
commit file lane-second lane-second
git push --quiet origin HEAD
second=$(git rev-parse HEAD)
far_gate "$second" > "$scratch/second-gate.out" 2>&1 &
second_gate=$!
pids+=("$second_gate")
sleep 1
[[ $(git -C "$clone" rev-parse HEAD) == "$first" ]] \
  || fail "#7758: a second far gate moved the clone before its first gate ended" "$(git -C "$clone" rev-parse HEAD)"
[[ $(< "$scratch/second-gate.out") == "gate-lane-flex-a: waiting on gate:remote of $first (pid"* ]] \
  || fail "#7758: a second far gate named no first gate while it waited" "$(< "$scratch/second-gate.out")"
touch "$scratch/home-far/release"
wait "$first_gate" || fail "#7758: the first far gate did not finish after release" "$(< "$scratch/first-gate.out")"
wait "$second_gate" || fail "#7758: the second far gate did not finish after the first" "$(< "$scratch/second-gate.out")"
[[ $(git -C "$clone" rev-parse HEAD) == "$second" ]] \
  || fail "#7758: the second far gate did not move the clone after the first ended" "$(git -C "$clone" rev-parse HEAD)"
rm -f "$scratch/home-far/held" "$scratch/home-far/hold" "$scratch/home-far/release"

# A far gate stops when the local end closes its SSH session. Its lane lock and
# host slot return within one second.
gate_released() {
  GANDR_HOST_LOCK_DIR=$scratch/locks bash -c '
    source "$1"
    host_lock --no-wait --fd 7 gate-lane-work 1 probe
    host_unlock 7
    host_lock --no-wait --fd 7 gate 1 probe
    host_unlock 7
  ' _ "$config_dir/mise/host-lock.bash" > /dev/null 2>&1
}
touch "$scratch/home-far/hold"
commit file session session
GANDR_REMOTE_SESSION_CASE=1 perl -MPOSIX=setsid -e 'setsid() or die "setsid\n"; exec @ARGV' \
  bash "$here/remote.bash" far > "$scratch/session.out" 2>&1 &
local_gate=$!
pids+=("$local_gate")
tries=0
until [[ -e $scratch/home-far/held ]]; do
  (( ++tries < 100 )) || { fail "#7714: the far gate never reached its held check" "$(< "$scratch/session.out")"; break; }
  sleep 0.1
done
far_groups+=("$(< "$scratch/home-far/session-group")")
kill -TERM "$local_gate" || :
wait "$local_gate" || :
released=false
for (( tries = 0; tries < 10; tries++ )); do
  if gate_released; then released=true; break; fi
  sleep 0.1
done
rm -f "$scratch/home-far/held" "$scratch/home-far/hold"
[[ $released == true ]] \
  || fail "#7714: a far gate whose local end stops gives back its lane lock and slot within one second" "$(< "$scratch/session.out")"

# Work that HEAD does not hold is refused before any push.
printf 'more\n' >> file
status=0
out=$("$here/remote.bash" far 2>&1) || status=$?
[[ $status == 2 && $out == *'the work holds changes that HEAD does not'* ]] \
  || fail "#6996: work that HEAD does not hold is refused" "exit $status, $out"
git checkout --quiet -- file

# The probe counts the gate slots that no gate holds: one of one with none
# held, none with its one slot held. It reads a token where the host's gh
# gives the reader's token, and none where it gives no token of the reader.
probe() {
  env -u GH_TOKEN PATH="$scratch/far-bin:$PATH" GANDR_GATE_SLOTS=1 GANDR_HOST_LOCK_DIR="$scratch/locks" \
    bash "$here/far.bash" probe "$scratch/far-checkout" "$1" | jq -c '[.free, .token]'
}
mkdir -p "$scratch/locks"
free=$(probe reader)
GANDR_HOST_LOCK_DIR=$scratch/locks bash -c 'source "$1"; host_lock --no-wait gate 1 holder; : > "$2/held"; exec sleep 300' _ "$config_dir/mise/host-lock.bash" "$scratch" > /dev/null 2>&1 &
pids+=("$!")
tries=0
until [[ -e $scratch/held ]]; do
  (( ++tries < 100 )) || { fail "#6996: the holder of the probe's slot never took it" ""; break; }
  sleep 0.1
done
held=$(probe other)
[[ $free == '[1,true]' && $held == '[0,false]' ]] \
  || fail "#6996: the probe counts the free gate slots and reads whether the host gives the reader's token" "free $free, then $held with the slot held and another reader"

(( failed == 0 )) || exit 1
echo "remote gate OK: a far pass with a reader's token lands here and publishes its verdict record after the push, this host's token goes to the far gate in no argument and no line, a far red records nothing, a far host that lacks a tool stops before its gate, a second far gate waits before it moves a shared clone, a far gate gives back its locks when its local end stops, work beyond HEAD is refused, and the probe counts the free slots and reads the reader's token"
