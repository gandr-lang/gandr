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
# and listing, and the push still goes through. A third, `update-refs`, sets
# `rebase.updateRefs` in the clone and puts its branch `kept` on the old tip
# of `landing`, as a seat's clone holds branches into the range. The caller
# stays in its own clone, and it fetches the origin again.
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
  if [[ ${3:-} == update-refs ]]; then
    git config rebase.updateRefs true
    git branch --quiet kept origin/landing
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

# A commit that main holds under another hash is dropped, not replayed: a
# fix on main after the copy changes the same line, and the replay would
# conflict with it. Landing's later landing moves onto main. The clone sets
# `rebase.updateRefs`, and its branch on the old tip stays there (#5932).
got=$(
  setup "$scratch/held"
  land pr1 shared $'one\nlanded\nthree'
  git checkout --quiet -b fixed "$(git rev-parse landing^)"
  git cherry-pick -x "$(git rev-parse landing^2)" > /dev/null
  commit shared $'one\nfixed\nthree' fix
  git push --quiet origin fixed:main
  git checkout --quiet landing
  land pr2 two 'two'
  old=$(git rev-parse landing)
  status=$(run "$scratch/held" '' update-refs) && again
  new=$(git rev-parse origin/landing)
  echo "exit $status," \
    "$(git merge-base --is-ancestor origin/main "$new" && echo "holds main," || echo "lacks main,")" \
    "shared $(git show "$new:shared" | sed -n 2p), two $(git show "$new:two")," \
    "kept $([[ $(git -C "$scratch/held/runner" rev-parse kept) == "$old" ]] && echo stays || echo moves)"
)
[[ $got == "exit 0, holds main, shared fixed, two two, kept stays" ]] || fail "#5932: a commit main holds under another hash is dropped, landing moves onto main, and no other branch moves" "$got"

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

# A fix on main while the merge queue builds a group on landing: the rebase
# waits, and landing stays while the group's branch stands. Once the group's
# branch goes, as the queue merges it, landing moves onto main (#6553).
got=$(
  setup "$scratch/queued"
  land pr1 one 'one'
  fix landing shared $'one\nfixed\nthree'
  land pr2 two 'two'
  before=$(git rev-parse landing)
  git push --quiet origin landing:refs/heads/gh-readonly-queue/landing/pr-3-0000000
  (REBASE_QUEUE_POLL=1 run "$scratch/queued" > "$scratch/queued/status") &
  waiter=$!
  sleep 3
  held=$([[ $(git ls-remote origin refs/heads/landing) == "$before"* ]] && echo stays || echo moves)
  git push --quiet origin --delete gh-readonly-queue/landing/pr-3-0000000
  wait "$waiter"
  again
  echo "while queued $held," \
    "exit $(< "$scratch/queued/status")," \
    "$(git merge-base --is-ancestor origin/main origin/landing && echo "then holds main" || echo "then lacks main")"
)
[[ $got == "while queued stays, exit 0, then holds main" ]] || fail "#6553: the rebase waits while the queue builds a group on landing, then moves landing" "$got"

# A group that the queue still builds when the wait ends: the push goes
# through, and the error names the group that the queue builds again.
got=$(
  setup "$scratch/overdue"
  land pr1 one 'one'
  fix landing shared $'one\nfixed\nthree'
  land pr2 two 'two'
  git push --quiet origin landing:refs/heads/gh-readonly-queue/landing/pr-3-0000000
  status=$(REBASE_QUEUE_WAIT=0 run "$scratch/overdue") && again
  echo "exit $status," \
    "$(git merge-base --is-ancestor origin/main origin/landing && echo "holds main," || echo "lacks main,")" \
    "$([[ $(< "$scratch/overdue/err") == *"build each again: pr-3-0000000"* ]] && echo "names the group" || echo "names no group")"
)
[[ $got == "exit 0, holds main, names the group" ]] || fail "#6553: past the wait the push goes through and names the group the queue builds again" "$got"

(( failed == 0 )) || exit 1
echo "landing rebase OK: 8 cases stay, fast-forward, move, stop on a conflict, drop what main holds, stop on a refused fetch, wait for the queue and end the wait as recorded"
