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
# item's own lines changes its record at the base. A head that does not hold
# the group's base reads its change from their merge base (#6999).
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

# A queue entry whose head does not hold the group's base (#6999): the
# architect signs the change itself, and an entry ahead of it lands a file
# that the change does not touch. The change runs from the merge base of the
# base and the head, so that file moves no patch. Read from the base, the
# diff holds the base's own file, as the queue read it for pull request 6995.
git -C "$repo" checkout --quiet landing
printf 'pub fn ahead() {}\n' > "$repo/src/ahead.rs"
ahead=$(commit ahead)
from=$(cd "$repo" && change_base "$ahead" "$signed")
[[ $from == "$(git -C "$repo" merge-base "$ahead" "$signed")" ]] \
  || fail "#6999: the change of a head that does not hold the base runs from their merge base" "$from"
got=$(cd "$repo" && moved "$fork" "$signed" "$from" "$signed" | tr '\n' ' ')
[[ -z $got ]] || fail "#6999: a file that only the group's base changes moves no patch of a head that does not hold it" "$got"
got=$(cd "$repo" && moved "$fork" "$signed" "$ahead" "$signed" | tr '\n' ' ')
[[ -n $got ]] || fail "#6999: the diff from the base itself holds the base's own file" "none"
from=$(cd "$repo" && change_base "$base" "$head")
[[ $from == "$base" ]] || fail "#6999: the change of a head that holds the base runs from the base" "$from"

# The merge queue's clone is shallow (#6920). The architect signs a commit,
# and the restack leaves it on no branch. The queue's clone fetches it by its
# name at depth 1, so the clone holds no fork. `signed_fork` fetches the two
# lines and reads the fork. GitHub leaves a commit fetched by its name at
# depth 1 under a `--deepen`, and a local origin deepens it, so the case reads
# the fork that `signed_fork` gives, not the refusal of the old deepening.
origin=$work/origin
git init --quiet --initial-branch landing "$origin"
git -C "$origin" config user.email cases@example.invalid
git -C "$origin" config user.name cases
git -C "$origin" config uploadpack.allowAnySHA1InWant true
at() { git -C "$origin" commit --quiet --no-verify --allow-empty -m "$1" && git -C "$origin" rev-parse HEAD; }
at root > /dev/null
shallow_fork=$(at fork)
git -C "$origin" checkout --quiet -b change
at signed-parent > /dev/null
shallow_signed=$(at signed)
git -C "$origin" checkout --quiet landing
git -C "$origin" branch --quiet -D change
at below > /dev/null
shallow_base=$(at base)
git clone --quiet --depth=1 --branch landing "file://$origin" "$work/clone" 2> /dev/null
git -C "$work/clone" fetch --quiet --depth=1 origin "$shallow_signed" 2> /dev/null
got=$(git -C "$work/clone" merge-base "$shallow_signed" "$shallow_base" 2> /dev/null) || got=none
[[ $got == none ]] || fail "#6920: a shallow clone that fetched the signed commit at depth 1 holds no fork, as the queue's clone does" "$got"
got=$(cd "$work/clone" && signed_fork "$shallow_signed" "$shallow_base") || got=none
[[ $got == "$shallow_fork" ]] || fail "#6920: in a shallow clone, the fork of a signed commit that no branch holds is read" "$got"

(( failed == 0 )) || exit 1
echo "deletes moved OK: a restack over rows that a landing adds keeps the sign-off; a change to its own lines or a new file moves it; a row below that names the item joins its readers; an edit below of its own lines changes its record; a head that does not hold the group's base reads its change from their merge base; a shallow clone reads the fork of a signed commit on no branch"
