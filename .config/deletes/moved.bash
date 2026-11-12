# shellcheck shell=bash
# The files whose own patch moved since a sign-off (#6852). `moved <fork>
# <sha> <from> <head>` prints each file whose patch differs between the
# change at the sign-off and the change now, one for each line. The change at
# the sign-off runs from `<fork>`, the merge base of `<sha>` with the base, to
# `<sha>`. The change now runs from `<from>` to `<head>`, where `<from>` is
# `change_base`'s. `git patch-id --stable` names each patch of one file, read
# with no context lines, so the rows that a landing below adds to a shared
# file move no patch. A restack over such a landing then keeps the sign-off,
# as the restack of pull request 6848 over the purpose rows of
# `ledger/purposes.sql` did not. A sign-off with no fork in the clone binds
# neither half, and `check.bash` reads it as stale.
moved() {
  local fork=$1 sha=$2 from=$3 head=$4 file
  patch() { git diff --no-renames --unified=0 "$1" "$2" -- "$3" | git patch-id --stable | awk '{ print $1 }'; }
  { git diff --no-renames --name-only "$fork" "$sha"; git diff --no-renames --name-only "$from" "$head"; } | sort -u \
    | while IFS= read -r file; do
      [[ $(patch "$fork" "$sha" "$file") == "$(patch "$from" "$head" "$file")" ]] || printf '%s\n' "$file"
    done
}

# The commit that a change runs from (#6999). `change_base <base> <head>`
# prints the merge base of `<base>` and `<head>`. A merge queue entry's head
# need not hold the group's base: the entry ahead of it lands after the
# entry's last push. The diff from `<base>` then holds the base's own
# changes as the entry's, and a sign-off turns stale on a file that only the
# base changes, as pull request 6995 did on `.config/stall/cases.json`. The
# shallow clone of the queue deepens `<base>` by 500 commits once when it
# holds no merge base. With none after that, it prints `<base>`, which reads
# no less of the change.
change_base() {
  local base=$1 head=$2
  git merge-base "$base" "$head" 2> /dev/null && return 0
  git fetch --quiet --deepen=500 origin "$base" 2> /dev/null || :
  git merge-base "$base" "$head" 2> /dev/null || git rev-parse "$base"
}

# The fork of a signed commit with the base (#6920). `signed_fork <sha>
# <base>` prints the merge base of `<sha>` and `<base>`, and fails when the
# clone holds none. The merge queue's clone is shallow, and the check fetches
# a signed commit by its name at depth 1. `git fetch --deepen` does not
# deepen a commit that the clone holds at depth 1 by its name alone, so the
# deepening gave no fork for pull request 6914. An explicit `--depth` on the
# signed commit gives its line, and `--deepen` on the base gives the base's.
# Each fetch reads at most 500 commits, and it runs only when the clone holds
# no fork.
signed_fork() {
  local sha=$1 base=$2
  git merge-base "$sha" "$base" 2> /dev/null && return 0
  git fetch --quiet --depth=500 origin "$sha" 2> /dev/null || :
  git fetch --quiet --deepen=500 origin "$base" 2> /dev/null || :
  git merge-base "$sha" "$base" 2> /dev/null
}

# The item's half of a sign-off (#6852). A restack can keep the change's own
# patch and still change what the deletion means. The architect reads the
# item as it stands at the base, with its readers, so the check binds both.
#
# `joined <fork> <base> <name>` prints each file at `<base>` that names
# `<name>` and that names it nowhere at `<fork>`, one for each line. Such a
# file is a new reader of the item, a ledger row or a README line among them.
joined() {
  local fork=$1 base=$2 name=$3
  comm -13 <(git grep -l -F -e "$name" "$fork" 2> /dev/null | sed "s|^$fork:||" | sort) \
    <(git grep -l -F -e "$name" "$base" 2> /dev/null | sed "s|^$base:||" | sort)
}

# `reshaped <fork> <base> <file> <start> <end>` succeeds when the record of
# an item, at lines `<start>` to `<end>` of `<file>` at `<base>`, changes
# from `<fork>` to `<base>`. A hunk of the diff with no context lines that
# meets those lines changes it. A file that `<fork>` lacks changes it too.
reshaped() {
  local fork=$1 base=$2 file=$3 start=$4 end=$5
  git cat-file -e "$fork:$file" 2> /dev/null || return 0
  git diff --no-renames --unified=0 "$fork" "$base" -- "$file" | awk -v s="$start" -v e="$end" '
    /^@@ / {
      n = split(substr($3, 2), at, ",")
      c = at[1] + 0
      d = n > 1 ? at[2] + 0 : 1
      if (d == 0) { if (c >= s && c < e) hit = 1 }
      else if (c <= e && c + d - 1 >= s) hit = 1
    }
    END { exit hit ? 0 : 1 }'
}
