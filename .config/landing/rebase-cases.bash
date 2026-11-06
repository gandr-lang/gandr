#!/usr/bin/env bash
# The rebase of `landing` onto `main` (#5441, `rebase.bash`), run by
# `check:landing-queue`. Each case builds a bare `origin` with `main` and
# `landing`, lands pull requests on `landing` as merge commits, and moves
# `main` as a green cycle moves it. Then it runs the rebase in a clone with
# a scratch signing key and reads `origin` again.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
rebase=$here/rebase.bash
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "landing rebase case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A bare origin at `$1/origin.git` whose `main` and `landing` hold one commit,
# and a working clone `$1/work` on `landing`.
setup() {
  git init --quiet --bare -b main "$1/origin.git"
  git init --quiet -b main "$1/work"
  cd "$1/work"
  identity
  printf 'one\ntwo\nthree\n' > shared
  git add shared && git commit --quiet -m base
  git remote add origin "$1/origin.git"
  git push --quiet origin main main:landing
  git checkout --quiet -b landing
}

# Lands the pull request `$1`, one commit that writes `$3` as the whole of
# the file `$2`, on `landing` as the queue lands it: a merge commit.
land() {
  git checkout --quiet -b "$1" landing
  commit "$2" "$3" "$1"
  git checkout --quiet landing
  git merge --quiet --no-ff -m "Merge $1" "$1"
  git push --quiet origin landing
}

# Moves `main` to `landing`'s commit `$1` and a fix on it that writes `$3` as
# the whole of `$2`, as a green cycle on `integration` moves it.
fix() {
  git checkout --quiet -b fixed "$1"
  commit "$2" "$3" fix
  git push --quiet origin fixed:main
  git checkout --quiet landing
}
# Runs the rebase in a clone of the origin with a scratch signing key, and
# prints its exit status. The rebase's errors go to `$1/err`. A second
# argument names the clone's upload-pack program: `false` refuses each fetch
# and listing, and the push still goes through. The caller stays in its own
# clone, and it fetches the origin again.
run() {
  local status=0
  git clone --quiet "$1/origin.git" "$1/runner"
  ssh-keygen -q -t ed25519 -N '' -C case -f "$1/key"
  printf 'case@example.invalid %s\n' "$(< "$1/key.pub")" > "$1/allowed"
  cd "$1/runner"
  identity
  git config gpg.format ssh
  git config gpg.ssh.program ssh-keygen
  git config user.signingkey "$1/key.pub"
  git config gpg.ssh.allowedSignersFile "$1/allowed"
  if [[ -n ${2:-} ]]; then
    git config remote.origin.uploadpack "$2"
  fi
  "$rebase" > /dev/null 2> "$1/err" || status=$?
  echo "$status"
}

# The origin's refs and notes, read again in the working clone.
again() {
  git fetch --quiet origin '+refs/heads/*:refs/remotes/origin/*'
  if git ls-remote --exit-code origin refs/notes/rebased > /dev/null; then
    git fetch --quiet origin '+refs/notes/rebased:refs/notes/rebased'
  fi
}

# A landing that holds main needs nothing: `landing` stays.
got=$(
  setup "$scratch/holds"
  land pr1 one 'one'
  before=$(git rev-parse landing)
  status=$(run "$scratch/holds") && again
  echo "exit $status, $([[ $(git rev-parse origin/landing) == "$before" ]] && echo stays || echo moves)"
)
[[ $got == "exit 0, stays" ]] || fail "#5441: a landing that holds main stays" "$got"

# A landing with no commit past main fast-forwards to main.
got=$(
  setup "$scratch/forward"
  fix landing other 'fixed'
  status=$(run "$scratch/forward") && again
  echo "exit $status, $([[ $(git rev-parse origin/landing) == "$(git rev-parse origin/main)" ]] && echo "main" || echo "not main")"
)
[[ $got == "exit 0, main" ]] || fail "#5441: a landing with nothing past main fast-forwards to it" "$got"

# A fix on main moves landing's later landings onto main: each new commit
# signed, the merge kept, and each old commit noted with its new hash.
got=$(
  setup "$scratch/moved"
  land pr1 one 'one'
  fix landing shared $'one\nfixed\nthree'
  land pr2 two 'two'
  old=$(git rev-parse landing)
  status=$(run "$scratch/moved") && again
  new=$(git rev-parse origin/landing)
  echo "exit $status," \
    "$(git merge-base --is-ancestor origin/main "$new" && echo "holds main," || echo "lacks main,")" \
    "$(git rev-list --count --merges origin/main.."$new") merge," \
    "$(git -c gpg.ssh.program=ssh-keygen -c gpg.ssh.allowedSignersFile="$scratch/moved/allowed" \
      log --format=%G? origin/main.."$new" | sort -u | paste -sd ' ' -) signed," \
    "$([[ $(git notes --ref=rebased show "$old") == "$new" ]] && echo noted || echo "not noted")"
)
[[ $got == "exit 0, holds main, 1 merge, G signed, noted" ]] || fail "#5441: a fix on main moves landing's landings onto it, signed and noted" "$got"

# A landing that conflicts with the fix stops before the push: landing stays.
got=$(
  setup "$scratch/conflict"
  land pr1 one 'one'
  fix landing shared $'one\nfixed\nthree'
  land pr2 shared $'one\nother\nthree'
  before=$(git rev-parse landing)
  status=$(run "$scratch/conflict") && again
  echo "exit $status, $([[ $(git rev-parse origin/landing) == "$before" ]] && echo stays || echo moves)"
)
[[ $got == "exit 3, stays" ]] || fail "#5441: a landing that conflicts with the fix stays as it was" "$got"

# A refused fetch stops the attempt before the rebase: landing stays, and the
# error names the fetch. The clone's refs from before would rebase landing,
# and the push would go through (#5627).
got=$(
  setup "$scratch/refused"
  land pr1 one 'one'
  fix landing shared $'one\nfixed\nthree'
  land pr2 two 'two'
  before=$(git rev-parse landing)
  status=$(run "$scratch/refused" false) && again
  echo "exit $status," \
    "$([[ $(git rev-parse origin/landing) == "$before" ]] && echo stays || echo moves)," \
    "$([[ $(< "$scratch/refused/err") == *"git fetch of main and landing"* ]] && echo "names the fetch" || echo "names no fetch")"
)
[[ $got == "exit 1, stays, names the fetch" ]] || fail "#5627: a refused fetch stops the rebase, and landing stays" "$got"

(( failed == 0 )) || exit 1
echo "landing rebase OK: 5 cases stay, fast-forward, move, stop on a conflict and stop on a refused fetch as recorded"
