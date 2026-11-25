#!/usr/bin/env bash
# The landing rebase (#5441, `rebase.bash`) and its trigger (`fixes.bash`,
# #6683), run by `check:landing-queue`. Each case builds a bare `origin` with
# `main`, `integration` and `landing`, lands pull requests on `landing` as
# merge commits, and moves `integration` and `main` as a green cycle moves
# them. Then it reads the trigger, runs the rebase in a clone with a scratch
# signing key and reads `origin` again. The act after the push (#6700,
# `REBASE_MOVED`) is a recorder: it writes the file `moved` beside the clone.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
rebase=$here/rebase.bash
fixes=$here/fixes.bash
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
printf '#!/usr/bin/env bash\ntouch ../moved\n' > "$scratch/moved-act"
chmod +x "$scratch/moved-act"
export REBASE_MOVED=$scratch/moved-act

fail() {
  echo "landing rebase case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A bare origin at `$1/origin.git` whose `main`, `integration` and `landing`
# hold one commit, and a working clone `$1/work` on `landing`.
setup() {
  git init --quiet --bare -b main "$1/origin.git"
  git init --quiet -b main "$1/work"
  cd "$1/work"
  identity
  printf 'one\ntwo\nthree\n' > shared
  git add shared && git commit --quiet -m base
  git remote add origin "$1/origin.git"
  git push --quiet origin main main:landing main:integration
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

# Moves `integration` and `main` to `landing`'s commit `$1` and a fix on it
# that writes `$3` as the whole of `$2`: the cycle takes `$1`, the fixer
# commits the fix on `integration`, and a green cycle moves `main` there.
fix() {
  git checkout --quiet -b fixed "$1"
  commit "$2" "$3" fix
  git push --quiet origin fixed:integration fixed:main
  git checkout --quiet landing
}

# Takes the tip of `landing` into `integration` with a merge, as the cycle
# takes it once `integration` holds a commit of its own. `main` stays.
take() {
  git fetch --quiet origin integration
  git checkout --quiet -B took FETCH_HEAD
  git merge --quiet --no-ff -m "Merge landing" landing
  git push --quiet origin took:integration
  git checkout --quiet landing
}

# The fixes that the cycle's trigger reads, one per line, after a fetch.
trigger() {
  git fetch --quiet origin '+refs/heads/*:refs/remotes/origin/*'
  "$fixes" origin/main origin/landing
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
  echo "exit $status, $([[ $(git rev-parse origin/landing) == "$before" ]] && echo stays || echo moves), $([[ -e $scratch/holds/moved ]] && echo restacks || echo "no restack")"
)
[[ $got == "exit 0, stays, no restack" ]] || fail "#5441, #6700: a landing that holds main stays, and no stack is restacked" "$got"

# One patch under two hashes: the fixer copies landing's commit onto
# integration, and the cycle then takes landing. `main` holds the copy and
# the merge, and `landing` holds the commit. The trigger reads no fix, so
# the job does not run, and a rebase by hand leaves `landing` as it is.
got=$(
  setup "$scratch/copied"
  land pr1 shared $'one\nlanded\nthree'
  git checkout --quiet -b copied main
  git cherry-pick "$(git rev-parse landing^2)" > /dev/null
  git merge --quiet --no-ff -m "Merge landing" landing
  git push --quiet origin copied:integration copied:main
  git checkout --quiet landing
  before=$(git rev-parse landing)
  read_fixes=$(trigger | wc -l | tr -d ' ')
  status=$(run "$scratch/copied") && again
  echo "$read_fixes fixes, exit $status, $([[ $(git rev-parse origin/landing) == "$before" ]] && echo stays || echo moves)"
)
[[ $got == "0 fixes, exit 0, stays" ]] || fail "#6683: one patch under two hashes on main and landing is no fix, so the rebase job does not run" "$got"

# A true fix on main that landing lacks. The cycle that moves main takes a
# newer head of landing into integration first, as on 2026-11-11, and a
# landing then stands above that head. The fix goes on the head that
# integration took, signed, and only the commits above it move: the merge
# kept and the old tip noted with its new hash.
got=$(
  setup "$scratch/moved"
  land pr1 one 'one'
  fix landing shared $'one\nfixed\nthree'
  land pr2 two 'two'
  take
  floor=$(git rev-parse landing)
  land pr3 three 'three'
  old=$(git rev-parse landing)
  read_fixes=$(trigger | wc -l | tr -d ' ')
  status=$(run "$scratch/moved") && again
  new=$(git rev-parse origin/landing)
  echo "$read_fixes fix, exit $status," \
    "$(git merge-base --is-ancestor "$floor" "$new" && echo "floor kept," || echo "floor moved,")" \
    "$(git rev-list --count --no-merges "$floor..$new") moved past the floor," \
    "$(git rev-list --count --merges "$floor..$new") merge," \
    "$(git -c gpg.ssh.program=ssh-keygen -c gpg.ssh.allowedSignersFile="$scratch/moved/allowed" \
      log --format=%G? "$floor..$new" | sort -u | paste -sd ' ' -) signed," \
    "shared $(git show "$new:shared" | sed -n 2p)," \
    "$([[ $(git notes --ref=rebased show "$old") == "$new" ]] && echo noted || echo "not noted")," \
    "then $("$fixes" origin/main origin/landing | wc -l | tr -d ' ') fixes," \
    "$([[ -e $scratch/moved/moved ]] && echo restacks || echo "no restack")"
)
[[ $got == "1 fix, exit 0, floor kept, 2 moved past the floor, 1 merge, G signed, shared fixed, noted, then 0 fixes, restacks" ]] \
  || fail "#6683, #6700: a true fix on main goes on the head that integration took, only the commits above it move, and the open stacks are restacked" "$got"

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

# A commit that main holds under another hash is no fix, and the rebase does
# not replay it: a fix on main after the copy changes the same line, and a
# replay of the copy would conflict with it. The fix goes on the head that
# integration took, and landing's later landing moves onto it. The clone
# sets `rebase.updateRefs`, and its branch on the old tip stays (#5932).
got=$(
  setup "$scratch/held"
  land pr1 shared $'one\nlanded\nthree'
  git checkout --quiet -b fixed main
  git cherry-pick "$(git rev-parse landing^2)" > /dev/null
  git merge --quiet --no-ff -m "Merge landing" landing
  commit shared $'one\nfixed\nthree' fix
  git push --quiet origin fixed:integration fixed:main
  git checkout --quiet landing
  floor=$(git rev-parse landing)
  land pr2 two 'two'
  old=$(git rev-parse landing)
  status=$(run "$scratch/held" '' update-refs) && again
  new=$(git rev-parse origin/landing)
  echo "exit $status," \
    "$(git merge-base --is-ancestor "$floor" "$new" && echo "floor kept," || echo "floor moved,")" \
    "shared $(git show "$new:shared" | sed -n 2p), two $(git show "$new:two")," \
    "kept $([[ $(git -C "$scratch/held/runner" rev-parse kept) == "$old" ]] && echo stays || echo moves)"
)
[[ $got == "exit 0, floor kept, shared fixed, two two, kept stays" ]] || fail "#5932: a commit main holds under another hash is no fix, the fix goes on the floor, and no other branch moves" "$got"

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
    "$([[ $(< "$scratch/refused/err") == *"git fetch of main, landing and integration"* ]] && echo "names the fetch" || echo "names no fetch")"
)
[[ $got == "exit 1, stays, names the fetch" ]] || fail "#5627: a refused fetch stops the rebase, and landing stays" "$got"

# A fix on main while the merge queue builds a group on landing: the rebase
# waits, and landing stays while the group's branch stands. Once the group's
# branch goes, as the queue merges it, landing takes the fix (#6553).
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
    "then $("$fixes" origin/main origin/landing | wc -l | tr -d ' ') fixes"
)
[[ $got == "while queued stays, exit 0, then 0 fixes" ]] || fail "#6553: the rebase waits while the queue builds a group on landing, then landing takes the fix" "$got"

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
    "then $("$fixes" origin/main origin/landing | wc -l | tr -d ' ') fixes," \
    "$([[ $(< "$scratch/overdue/err") == *"build each again: pr-3-0000000"* ]] && echo "names the group" || echo "names no group")"
)
[[ $got == "exit 0, then 0 fixes, names the group" ]] || fail "#6553: past the wait the push goes through and names the group the queue builds again" "$got"

(( failed == 0 )) || exit 1
echo "landing rebase OK: 8 cases stay, read no fix in a copy, put a true fix on the floor and move only the commits above it, stop on a conflict, skip what main holds, stop on a refused fetch, wait for the queue and end the wait as recorded"
