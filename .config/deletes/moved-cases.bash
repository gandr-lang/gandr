#!/usr/bin/env bash
# The cases of `moved.bash`, run by `check:deletes`. The architect signed the
# deletion of pull request 6848 at one commit. The stack below it landed and
# added purpose rows to `ledger/purposes.sql`, which the change shares, and
# the restack turned the sign-off stale (#6852). The cases build a scratch
# repository with a signed change to a shared file and a landing below it.
# A row that the landing adds moves no word, so the sign-off holds. An edit
# of another cell of a line that names the item moves nothing, as the `since`
# cells of pull request 7017 did (#7025). A change to a word that names the
# item moves it, and so does a new file that names the item. The item's half
# holds the rest: a row below that names the item joins its readers, and an
# edit below of the item's own lines changes its record at the base. A head
# that does not hold the group's base reads its change from their merge base
# (#6999).
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
printf "INSERT INTO purpose VALUES (1);\nINSERT INTO purpose VALUES ('Gone', 2);\nINSERT INTO purpose VALUES (3);\n" > "$repo/ledger/purposes.sql"
printf 'pub enum E {\n    Kept,\n    Gone,\n}\n' > "$repo/src/error.rs"
fork=$(commit fork)

# The change: it drops a variant, and the shared file's row that names it
# names the kept variant.
git -C "$repo" checkout --quiet -b change
printf 'pub enum E {\n    Kept,\n}\n' > "$repo/src/error.rs"
printf "INSERT INTO purpose VALUES (1);\nINSERT INTO purpose VALUES ('Kept', 2);\nINSERT INTO purpose VALUES (3);\n" > "$repo/ledger/purposes.sql"
signed=$(commit change)

# The landing below adds an unrelated row at the end of the shared file.
git -C "$repo" checkout --quiet landing
printf 'INSERT INTO purpose VALUES (4);\n' >> "$repo/ledger/purposes.sql"
base=$(commit below)

# The restack: the same change on the new base.
git -C "$repo" checkout --quiet -b restacked
git -C "$repo" cherry-pick --quiet "$signed" > /dev/null
head=$(git -C "$repo" rev-parse HEAD)

got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$head" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#6852: a restack over a row that a landing below adds to a shared file moves no word, so the sign-off holds" "$got"

# An edit of another cell of the row that named the item moves nothing.
printf "INSERT INTO purpose VALUES (1);\nINSERT INTO purpose VALUES ('Kept', 21);\nINSERT INTO purpose VALUES (3);\nINSERT INTO purpose VALUES (4);\n" > "$repo/ledger/purposes.sql"
celled=$(commit celled)
got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$celled" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#7025: an edit of another cell of a line that names the item moves nothing" "$got"

# A change to a word that names the item after the sign-off moves it.
git -C "$repo" checkout --quiet --detach "$head"
printf "INSERT INTO purpose VALUES (1);\nINSERT INTO purpose VALUES ('Gone', 2);\nINSERT INTO purpose VALUES (3);\nINSERT INTO purpose VALUES (4);\n" > "$repo/ledger/purposes.sql"
edited=$(commit edited)
got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$edited" Gone | tr '\n' ' ')
[[ $got == $'Gone\tledger/purposes.sql ' ]] || fail "#6852: a change to a word that names the item after the sign-off moves that file alone" "$got"

# A file that the change starts to touch after the sign-off moves when its
# words name the item, and moves nothing when they do not.
git -C "$repo" checkout --quiet --detach "$head"
printf 'pub fn more() -> E { E::Gone }\n' > "$repo/src/more.rs"
more=$(commit more)
got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$more" Gone | tr '\n' ' ')
[[ $got == $'Gone\tsrc/more.rs ' ]] || fail "#6852: a new file that names the item after the sign-off moves" "$got"
git -C "$repo" checkout --quiet --detach "$head"
printf 'pub fn other() {}\n' > "$repo/src/other.rs"
other=$(commit other)
got=$(cd "$repo" && moved "$fork" "$signed" "$base" "$other" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#7025: a new file that names the item nowhere moves nothing" "$got"

# The item's half: a reader row that names the variant lands below the
# signed deletion. The change's words hold, and the row joins the readers.
git -C "$repo" checkout --quiet landing
printf "INSERT INTO reader VALUES ('Gone');\n" > "$repo/ledger/readers.sql"
reader=$(commit reader)
git -C "$repo" checkout --quiet -b restacked-reader
git -C "$repo" cherry-pick --quiet "$signed" > /dev/null
restacked=$(git -C "$repo" rev-parse HEAD)
fork2=$(git -C "$repo" merge-base "$signed" "$reader")
got=$(cd "$repo" && moved "$fork2" "$signed" "$reader" "$restacked" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#6852: a row below that names the item moves no word of the change" "$got"
got=$(cd "$repo" && joined "$fork2" "$reader" Gone | tr '\n' ' ')
[[ $got == 'ledger/readers.sql ' ]] || fail "#6852: a row below that names the item joins its readers at the base, so the sign-off turns stale with that file named" "$got"
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
# that names the item and that the change does not touch. The change runs
# from the merge base of the base and the head, so that file moves nothing.
# Read from the base, the diff holds the base's own file, as the queue read
# it for pull request 6995.
git -C "$repo" checkout --quiet landing
printf 'pub fn ahead() -> E { E::Gone }\n' > "$repo/src/ahead.rs"
ahead=$(commit ahead)
from=$(cd "$repo" && change_base "$ahead" "$signed")
[[ $from == "$(git -C "$repo" merge-base "$ahead" "$signed")" ]] \
  || fail "#6999: the change of a head that does not hold the base runs from their merge base" "$from"
got=$(cd "$repo" && moved "$fork" "$signed" "$from" "$signed" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#6999: a file that only the group's base changes moves nothing of a head that does not hold it" "$got"
got=$(cd "$repo" && moved "$fork" "$signed" "$ahead" "$signed" Gone | tr '\n' ' ')
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

# A sign-off whose commit no pushed ref holds (#7012). The seat of pull
# request 7009 rebased after the sign-off, so only its clone held the signed
# commit, and the queue's clone could not fetch it. GitHub serves no commit
# that a force-push leaves behind, so the case's `origin` drops the commit
# after the push that leaves it. `served` asks `origin` from a scratch
# repository, so a commit that the seat's clone holds reads as the queue
# reads it.
served_origin=$work/served-origin
git init --quiet --initial-branch landing "$served_origin"
git -C "$served_origin" config user.email cases@example.invalid
git -C "$served_origin" config user.name cases
git -C "$served_origin" config uploadpack.allowReachableSHA1InWant true
git -C "$served_origin" config uploadpack.allowFilter true
git -C "$served_origin" commit --quiet --no-verify --allow-empty -m root
git -C "$served_origin" checkout --quiet -b change
git -C "$served_origin" commit --quiet --no-verify --allow-empty -m pushed
pushed=$(git -C "$served_origin" rev-parse HEAD)
git -C "$served_origin" commit --quiet --no-verify --allow-empty -m 'pushed, then left behind'
left=$(git -C "$served_origin" rev-parse HEAD)
git clone --quiet "file://$served_origin" "$work/seat"
git -C "$work/seat" config user.email cases@example.invalid
git -C "$work/seat" config user.name cases
git -C "$work/seat" checkout --quiet change
git -C "$work/seat" commit --quiet --no-verify --allow-empty -m 'rebased, never pushed'
unpushed=$(git -C "$work/seat" rev-parse HEAD)
git -C "$served_origin" reset --quiet --hard "$pushed"
git -C "$served_origin" reflog expire --expire=now --all
git -C "$served_origin" gc --quiet --prune=now
(cd "$work/seat" && served "$work/scratch" "$unpushed") \
  && fail "#7012: a signed commit that only the seat's clone holds is not served, so the sign-off is stale" "served"
(cd "$work/seat" && served "$work/scratch" "$left") \
  && fail "#7012: a signed commit that a force-push leaves behind is not served" "served"
(cd "$work/seat" && served "$work/scratch" "$pushed") \
  || fail "#7012: a signed commit that a pushed ref holds is served, so the sign-off holds" "not served"

(( failed == 0 )) || exit 1
echo "deletes moved OK: a restack over rows that a landing adds keeps the sign-off; an edit of another cell of a line that names the item keeps it; a change to a word that names the item or a new file that names it moves it; a row below that names the item joins its readers; an edit below of its own lines changes its record; a head that does not hold the group's base reads its change from their merge base; a shallow clone reads the fork of a signed commit on no branch; a signed commit counts only when origin serves it"
