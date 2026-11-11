#!/usr/bin/env bash
# The cases of `moved.bash`, run by `check:deletes`. The architect signed the
# deletion of pull request 6848 at one commit. The stack below it landed and
# added purpose rows to `ledger/purposes.sql`, which the change shares, and
# the restack turned the sign-off stale (#6852). The cases build a scratch
# repository with a signed change to a shared file and a landing below it.
# A row that the landing adds moves no patch, so the sign-off holds. A change
# to the change's own lines moves the patch. A file that the change starts to
# touch after the sign-off moves too. The item's half holds the rest: a row
# below that names the item joins its readers, and an edit below of the
# item's own lines changes its record at the base.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/moved.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-moved.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0
fail() {
  echo "deletes moved case FAILED: $1"
  echo "  got: $2"
  failed=1
}

repo=$work/repo
mkdir -p "$repo/ledger" "$repo/src"
git -C "$repo" init --quiet --initial-branch landing
git -C "$repo" config user.email cases@example.invalid
git -C "$repo" config user.name cases
commit() { git -C "$repo" add -A && git -C "$repo" commit --quiet --no-verify -m "$1" && git -C "$repo" rev-parse HEAD; }
printf 'INSERT INTO purpose VALUES (1);\nINSERT INTO purpose VALUES (2);\nINSERT INTO purpose VALUES (3);\n' > "$repo/ledger/purposes.sql"
printf 'pub enum E {\n    Kept,\n    Gone,\n}\n' > "$repo/src/error.rs"
fork=$(commit fork)

# The change: it drops a variant and edits the second row of the shared file.
git -C "$repo" checkout --quiet -b change
printf 'pub enum E {\n    Kept,\n}\n' > "$repo/src/error.rs"
printf 'INSERT INTO purpose VALUES (1);\nINSERT INTO purpose VALUES (20);\nINSERT INTO purpose VALUES (3);\n' > "$repo/ledger/purposes.sql"
signed=$(commit change)

# The landing below adds an unrelated row at the end of the shared file.
git -C "$repo" checkout --quiet landing
printf 'INSERT INTO purpose VALUES (4);\n' >> "$repo/ledger/purposes.sql"
base=$(commit below)

# The restack: the same change on the new base.
git -C "$repo" checkout --quiet -b restacked
git -C "$repo" cherry-pick --quiet "$signed" > /dev/null
head=$(git -C "$repo" rev-parse HEAD)

got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$head" | tr '\n' ' ')
[[ -z $got ]] || fail "#6852: a restack over a row that a landing below adds to a shared file moves no patch, so the sign-off holds" "$got"

# A change to the change's own row after the sign-off moves the patch.
printf 'INSERT INTO purpose VALUES (1);\nINSERT INTO purpose VALUES (21);\nINSERT INTO purpose VALUES (3);\nINSERT INTO purpose VALUES (4);\n' > "$repo/ledger/purposes.sql"
edited=$(commit edited)
got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$edited" | tr '\n' ' ')
[[ $got == 'ledger/purposes.sql ' ]] || fail "#6852: a change to the change's own lines after the sign-off moves the patch of that file alone" "$got"

# A file that the change starts to touch after the sign-off moves too.
git -C "$repo" checkout --quiet --detach "$head"
printf 'pub fn more() {}\n' > "$repo/src/more.rs"
more=$(commit more)
got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$more" | tr '\n' ' ')
[[ $got == 'src/more.rs ' ]] || fail "#6852: a file that the change starts to touch after the sign-off moves" "$got"

# The item's half: a purpose row that names the variant lands below the
# signed deletion. The change's patch holds, and the row joins the readers.
git -C "$repo" checkout --quiet landing
printf "INSERT INTO purpose VALUES ('Gone');\n" >> "$repo/ledger/purposes.sql"
reader=$(commit reader)
git -C "$repo" checkout --quiet -b restacked-reader
git -C "$repo" cherry-pick --quiet "$signed" > /dev/null
restacked=$(git -C "$repo" rev-parse HEAD)
fork2=$(git -C "$repo" merge-base "$signed" "$reader")
got=$(cd "$repo" && moved "$fork2" "$signed" "$reader" "$restacked" | tr '\n' ' ')
[[ -z $got ]] || fail "#6852: a row below that names the item moves no patch of the change" "$got"
got=$(cd "$repo" && joined "$fork2" "$reader" Gone | tr '\n' ' ')
[[ $got == 'ledger/purposes.sql ' ]] || fail "#6852: a row below that names the item joins its readers at the base, so the sign-off turns stale with that file named" "$got"
got=$(cd "$repo" && joined "$fork2" "$base" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#6852: a landing below that names the item nowhere adds no reader" "$got"

# An edit below of the item's own line changes its record at the base, and an
# edit of another line of the same file does not.
git -C "$repo" checkout --quiet landing
printf 'pub enum E {\n    Kept,\n    Gone(u8),\n}\n' > "$repo/src/error.rs"
recast=$(commit recast)
(cd "$repo" && reshaped "$fork" "$recast" src/error.rs 3 3) \
  || fail "#6852: an edit below of the item's own line changes its record at the base" "unchanged"
(cd "$repo" && reshaped "$fork" "$recast" src/error.rs 2 2) \
  && fail "#6852: an edit below of another line leaves the record of an item unchanged" "changed"
(cd "$repo" && reshaped "$fork" "$base" src/error.rs 3 3) \
  && fail "#6852: a landing below that leaves the file unchanged leaves the record unchanged" "changed"

(( failed == 0 )) || exit 1
echo "deletes moved OK: a restack over rows that a landing adds keeps the sign-off; a change to its own lines or a new file moves it; a row below that names the item joins its readers; an edit below of its own lines changes its record"
