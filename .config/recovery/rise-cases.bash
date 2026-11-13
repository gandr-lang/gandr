#!/usr/bin/env bash
# The cases of `rise.bash` (#6806), run by `check:recovery-rise`. Each case
# builds a scratch repository with the tree's layout: one corpus source, its
# recovery record and `tests/recovery-owed.tsv`. The base record's three
# dropped rows change at the head: the first rises, the second falls and the
# third changes its nodes alone.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
rise=$here/rise.bash
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
fail() {
  echo "recovery-rise: $*" >&2
  failed=1
}

records=crates/surface-parser/tests/recovery
owed=crates/surface-parser/tests/recovery-owed.tsv
record=$records/fixture/a.recovery
# A repository at `$1` whose base holds the source and the record of three
# dropped rows, and whose head re-records them.
setup() {
  git init -q -b main "$1"
  cd "$1"
  git config user.email case@example.invalid
  git config user.name case
  git config commit.gpgsign false
  mkdir -p corpus "$records/fixture"
  printf 'def a = 1\n' > corpus/a.gandr
  printf '# The dropped-token rows that read worse than they owe.\n' > "$owed"
  printf 'W\t0\t20\tdigest\nT\t0\t5\taaaaaaaa\t3\t18\nT\t0\t6\tbbbbbbbb\t4\t18\nT\t0\t7\tcccccccc\t1\t18\n' > "$record"
  git add . && git commit -q -m base
  printf 'W\t0\t20\tdigest\nT\t0\t5\taaaaaaaa\t5\t18\nT\t0\t6\tbbbbbbbb\t2\t18\nT\t0\t7\tcccccccc\t1\t22\n' > "$record"
}

# Unlisted, the rise is refused, and the fall and the nodes pass.
got=$(setup "$scratch/unlisted"; git commit -q -am re-record; if out=$("$rise" HEAD^ 2>&1); then echo "passed"; else echo "refused"; fi; printf '%s\n' "$out")
[[ $got == $'refused\nrecovery-rise: fixture/a.gandr drop 0: obligations 3 -> 5, a rise of 2; list it in tests/recovery-owed.tsv with the issue that owes 3, or repair it (#6806)' ]] \
  || fail "#6806: an unlisted rise was not refused alone, with its source, its token, its counts and its rise: $got"

# Listed with the issue that owes it, the rise passes.
got=$(setup "$scratch/listed"; printf 'fixture/a.gandr\t0\t3\t6806\n' >> "$owed"; git commit -q -am re-record; if out=$("$rise" HEAD^ 2>&1); then echo "passed"; else echo "refused"; fi; printf '%s' "$out")
[[ $got == passed ]] || fail "#6806: a rise that tests/recovery-owed.tsv lists was refused: $got"

# A change that edits the source holds other tokens, so its rows do not
# compare.
got=$(setup "$scratch/edited"; printf 'def a = 2\n' > corpus/a.gandr; git commit -q -am edit; if out=$("$rise" HEAD^ 2>&1); then echo "passed"; else echo "refused"; fi; printf '%s' "$out")
[[ $got == passed ]] || fail "#6806: a record whose source the change edits was compared row by row: $got"

# A record whose row count changes does not compare one to one.
got=$(setup "$scratch/count"; printf 'T\t0\t8\tdddddddd\t9\t18\n' >> "$record"; git commit -q -am grow; if out=$("$rise" HEAD^ 2>&1); then echo "passed"; else echo "refused"; fi; printf '%s' "$out")
[[ $got == passed ]] || fail "#6806: a record whose row count changes was compared row by row: $got"

# A base that does not read stops the run with its own status.
status=0
(setup "$scratch/unread"; git commit -q -am re-record; "$rise" 0000000000000000000000000000000000000000 > /dev/null 2>&1) || status=$?
[[ $status == 2 ]] || fail "#6806: a base that does not read gave status $status, not 2"

(( failed == 0 )) || exit 1
echo "recovery-rise check OK: an unlisted rise of a dropped row is refused with its counts, a listed rise passes, a fall and a change of nodes pass, and a record of an edited source or of another row count is read as a tree change"
