#!/usr/bin/env bash
# The readings of the toolchain follower (#4540, `follow.bash`'s
# `follow_once`), run by `check:follow`. Each case builds a bare `origin` with
# one commit on `main` and a main checkout that follows it, under scratch XDG
# directories and a scratch git configuration. A stub `cargo` on `PATH` ends
# its build as the case asks and counts its builds. A warm lock that a live
# process holds keeps `follow_warm` from starting the gates' builds. The pages
# go to a file.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "follow case FAILED: $1"
  echo "  got: $2"
  failed=1
}

mkdir "$scratch/bin"
cat > "$scratch/bin/cargo" << 'EOF'
#!/usr/bin/env bash
# The stub build. `STUB_CARGO` names how it ends: a signal ends it, it writes
# more than a pipe holds, cargo refuses it, it fetches the git dependency
# `STUB_DEPENDENCY`, or else it builds a stub `gandr`.
echo build >> "$STUB_BUILDS"
case ${STUB_CARGO:-} in
  signal) kill -TERM $$ ;;
  noisy)
    for line in $(seq 1 4096); do
      echo "   Compiling crate$line v0.0.0" || { echo "error: Broken pipe (os error 32)" >&2; exit 101; }
    done
    ;;
  refuse) echo 'error: could not compile `gandr-lang` (bin "gandr") due to 1 previous error' >&2; exit 101 ;;
  fetch) git ls-remote -q "$STUB_DEPENDENCY" > /dev/null || { echo "error: failed to fetch $STUB_DEPENDENCY" >&2; exit 101; } ;;
esac
mkdir -p target/release
printf '#!/usr/bin/env bash\n' > target/release/gandr
chmod +x target/release/gandr
EOF
printf '#!/usr/bin/env bash\n' > "$scratch/bin/mise"
chmod +x "$scratch/bin/cargo" "$scratch/bin/mise"
# A mise shim finds its configuration, its trust and its tools under the XDG
# directories, which each case moves, so mise's own directories stay put.
export MISE_CONFIG_DIR=${MISE_CONFIG_DIR:-${XDG_CONFIG_HOME:-$HOME/.config}/mise}
export MISE_STATE_DIR=${MISE_STATE_DIR:-${XDG_STATE_HOME:-$HOME/.local/state}/mise}
export MISE_DATA_DIR=${MISE_DATA_DIR:-${XDG_DATA_HOME:-$HOME/.local/share}/mise}
export PATH=$scratch/bin:$PATH GIT_CONFIG_NOSYSTEM=1

# A bare origin at `$1/origin.git` with one commit on `main`, its main
# checkout `$1/main` cloned by a `file://` URL, and the follower sourced over
# scratch XDG directories under `$1`, with its pages written to `$1/pages`.
setup() {
  export GIT_CONFIG_GLOBAL=$1/gitconfig XDG_CONFIG_HOME=$1/config XDG_STATE_HOME=$1/state XDG_DATA_HOME=$1/data
  export STUB_BUILDS=$1/builds
  mkdir -p "$1"
  : > "$GIT_CONFIG_GLOBAL"
  git init --quiet --bare -b main "$1/origin.git"
  git clone --quiet "file://$1/origin.git" "$1/main" 2> /dev/null
  (cd "$1/main" && identity && commit one one 'one' && git push --quiet origin main)
  mkdir -p "$XDG_STATE_HOME/gandr/follow.json.warming"
  echo "$$" > "$XDG_STATE_HOME/gandr/follow.json.warming/pid"
  cd "$here"
  source "$here/follow.bash"
  follow_page_command=(bash -c 'echo "$1" >> "$0"' "$1/pages")
}

# One reading of `$1/main` as `toolchain:follow` runs it, the stub build
# ending as `$2` names.
reading() { (export STUB_CARGO=$2 && follow_once "$1/main") > /dev/null 2>&1 || :; }

# The memory's field `$1`, or `none`.
remembered() { jq -r --arg key "$1" '.[$key] // "none"' <<< "$(follow_memory)"; }

# The pages sent and the builds run so far.
pages() { if [[ -f $1/pages ]]; then wc -l < "$1/pages" | tr -d ' '; else echo 0; fi; }
builds() { if [[ -f $STUB_BUILDS ]]; then wc -l < "$STUB_BUILDS" | tr -d ' '; else echo 0; fi; }

# A build that a signal ends records nothing and pages nothing, and the next
# reading builds the commit and deploys it.
got=$(
  setup "$scratch/signal"
  reading "$scratch/signal" signal
  echo "failed $(remembered failed), $(pages "$scratch/signal") pages," \
    "$(reading "$scratch/signal" ok && [[ $(remembered deployed) == $(git -C "$scratch/signal/main" rev-parse HEAD) ]] && echo deployed || echo "not deployed")"
)
[[ $got == "failed none, 0 pages, deployed" ]] || fail "#4540: a build that a signal ends records nothing and is built again" "$got"

# A build whose output pipe breaks, `SIGPIPE` ignored as a service has it,
# deploys: the build writes to its log, never to the follower's output.
got=$(
  setup "$scratch/pipe"
  { (trap '' PIPE && export STUB_CARGO=noisy && follow_once "$scratch/pipe/main") 2> /dev/null || :; } | true
  echo "failed $(remembered failed), $(pages "$scratch/pipe") pages," \
    "$([[ $(remembered deployed) == $(git -C "$scratch/pipe/main" rev-parse HEAD) ]] && echo deployed || echo "not deployed")"
)
[[ $got == "failed none, 0 pages, deployed" ]] || fail "#4540: a build whose output pipe breaks deploys" "$got"

# A build that cargo refuses records `failed` and pages once, and the next
# reading neither builds it nor pages again.
got=$(
  setup "$scratch/refuse"
  reading "$scratch/refuse" refuse
  reading "$scratch/refuse" refuse
  echo "$([[ $(remembered failed) == $(git -C "$scratch/refuse/main" rev-parse HEAD) ]] && echo failed || echo "not failed")," \
    "$(pages "$scratch/refuse") pages, $(builds) builds"
)
[[ $got == "failed, 1 pages, 1 builds" ]] || fail "a build that cargo refuses records failed and pages once" "$got"

# A user-level `insteadOf` that sends origin's owner to an unreachable host
# leaves the fetch, and the build's fetch of a git dependency of that owner,
# on the URLs they name: the reading deploys.
got=$(
  setup "$scratch/rewrite"
  git init --quiet --bare -b main "$scratch/rewrite/dependency.git"
  printf '[url "ssh://nowhere.invalid/"]\n\tinsteadOf = file://\n' > "$GIT_CONFIG_GLOBAL"
  export GIT_SSH_COMMAND=false STUB_DEPENDENCY="file://$scratch/rewrite/dependency.git"
  reading "$scratch/rewrite" fetch
  echo "$(pages "$scratch/rewrite") pages," \
    "$([[ $(remembered deployed) == $(git -C "$scratch/rewrite/main" rev-parse HEAD) ]] && echo deployed || echo "not deployed")"
)
[[ $got == "0 pages, deployed" ]] || fail "#4540: a user-level rewrite of origin's owner leaves the fetches on their URLs" "$got"

# One failed fetch pages nothing, the second in a row pages once, and the
# third pages nothing more for the same commit of `origin/main`.
got=$(
  setup "$scratch/fetch"
  git -C "$scratch/fetch/main" remote set-url origin "file://$scratch/fetch/gone.git"
  counts=()
  for _ in 1 2 3; do
    reading "$scratch/fetch" ok
    counts+=("$(pages "$scratch/fetch")")
  done
  echo "${counts[*]}"
)
[[ $got == "0 1 1" ]] || fail "#4540: the second failed fetch in a row pages, once" "$got"

(( failed == 0 )) || exit 1
echo "follow readings OK: 5 cases record, page and deploy as recorded"
