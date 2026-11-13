#!/usr/bin/env bash
# The gate on another host (#6996, `remote.bash` and `far.bash`), run by
# `check:gate-scope`. A stand-in `ssh` runs the far side on this host, with a
# home directory of its own for each host, and a stand-in `mise` there passes
# or fails the far gate and writes its record. A scratch bare repository is
# `origin`. This checkout's `.config` is linked into each scratch tree, so the
# far side runs the tree's own scripts. The cases read the record that comes
# here, the refusals and the probe's free slots. `choose.jq`'s cases in
# `cases.json` hold the choice of the host.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
config_dir=$(cd "$here/.." && pwd)
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
pids=()
cleanup() {
  local pid
  for pid in ${pids[@]+"${pids[@]}"}; do kill -KILL "$pid" 2> /dev/null || true; done
  rm -rf "$scratch"
}
trap cleanup EXIT
failed=0

fail() {
  echo "remote case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# The stand-in `ssh`: its first argument is the host, and the rest is the far
# command, which runs with that host's home and state directories and the
# stand-ins first on the path. An ssh session carries no `GH_TOKEN` of this
# host. It writes its arguments to `ssh-args`.
mkdir -p "$scratch/bin" "$scratch/far-bin" "$scratch/near-bin"
cat > "$scratch/bin/ssh" << EOF
#!/usr/bin/env bash
printf '%s\n' "\$*" >> $scratch/ssh-args
host=\$1
shift
unset GH_TOKEN
export HOME=$scratch/home-\$host XDG_STATE_HOME=$scratch/home-\$host/state PATH=$scratch/far-bin:\$PATH
mkdir -p "\$HOME"
exec bash -c "\$*"
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
# The stand-in `mise` of the far host: `trust` passes. `run tools:check`
# reads the host's tools: it names a lack and exits 2 when the host's home
# holds `lacks`. `run check` touches `gated` in the host's home and writes the
# record of the tree as `passed.bash record` does. It fails when the host's
# home holds `red`, or when the gate holds no reader's token. It writes the
# token it reads with to `token` in the host's home.
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
echo "remote gate OK: a far pass with a reader's token lands here with its host after the push, this host's token goes to the far gate in no argument and no line, a far red records nothing, a far host that lacks a tool stops before its gate, work beyond HEAD is refused, and the probe counts the free slots and reads the reader's token"
