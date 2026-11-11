# shellcheck shell=bash
# The files whose own patch moved since a sign-off (#6852). `moved <fork>
# <sha> <base> <head>` prints each file whose patch differs between the
# change at the sign-off and the change now, one for each line. The change at
# the sign-off runs from `<fork>`, the merge base of `<sha>` with `<base>`, to
# `<sha>`. The change now runs from `<base>` to `<head>`. `git patch-id
# --stable` names each patch of one file, read with no context lines, so the
# rows that a landing below adds to a shared file move no patch. A restack
# over such a landing then keeps the sign-off, as the restack of pull request
# 6848 over the purpose rows of `ledger/purposes.sql` did not. A sign-off
# with no fork in the clone binds neither half, and `check.bash` reads it as
# stale.
moved() {
  local fork=$1 sha=$2 base=$3 head=$4 file
  patch() { git diff --no-renames --unified=0 "$1" "$2" -- "$3" | git patch-id --stable | awk '{ print $1 }'; }
  { git diff --no-renames --name-only "$fork" "$sha"; git diff --no-renames --name-only "$base" "$head"; } | sort -u \
    | while IFS= read -r file; do
      [[ $(patch "$fork" "$sha" "$file") == "$(patch "$base" "$head" "$file")" ]] || printf '%s\n' "$file"
    done
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
