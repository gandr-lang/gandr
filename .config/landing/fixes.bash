#!/usr/bin/env bash
# The fixes on `main` that `landing` lacks (#6683): the trigger of the landing
# rebase in `ci:cycle`, and the commits that `rebase.bash` puts on `landing`.
# A fix is a commit of `main`, not on `landing` and not a merge, whose patch
# `landing` lacks. Git compares the patches by `git patch-id --stable`. So a
# merge of `landing` into `integration` is no fix, and a commit that
# `landing` holds under another hash is no fix either.
#
# `rev-list --cherry-pick` gives the candidates: it compares each commit of
# `main` past the merge base with the commits of `landing` past it. A copy of
# a candidate can stand below that merge base, as a fixer's copy does once
# both branches hold it (#6683: `4632b4cbd` copies `22212ad23`). So each
# candidate is compared again with the commits of `landing` past the merge
# base of the candidate and `landing`.
#
# Usage: fixes.bash <main> <landing>
#   Prints each fix, oldest first. It prints nothing when `landing` holds
#   every patch of `main`.
set -euo pipefail
main=${1:?main}
landing=${2:?landing}
for candidate in $(git rev-list --reverse --no-merges --right-only --cherry-pick "$landing...$main"); do
  patch=$(git show "$candidate" | git patch-id --stable)
  held=$(git log --no-merges -p "$(git merge-base "$candidate" "$landing")..$landing" | git patch-id --stable)
  [[ $'\n'$held == *$'\n'"${patch%% *} "* ]] || printf '%s\n' "$candidate"
done
