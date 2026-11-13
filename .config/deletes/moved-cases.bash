#!/usr/bin/env bash
# The cases of `moved.bash`, run by `check:deletes`. The architect signed the
# deletion of pull request 6848 at one commit. The stack below it landed and
# added purpose rows to `ledger/purposes.sql`, which the change shares, and
# the restack turned the sign-off stale (#6852). The cases build a scratch
# repository with a signed change to a shared file and a landing below it.
# A row that the landing adds moves no word, so the sign-off holds. An edit
# of another cell of a line that names the item moves nothing, as the `since`
# cells of pull request 7017 did (#7025). A change to a word that names the
# item moves it, and so does a new file that names the item. A file of the
# change names an item of a crate only as a Rust source of a crate that can
# name it, and a row or a script does not (#7164). The item's visibility
# bounds that reach: its module, its parent's, its crate or its package
# (#7209). A source that joins the item's readers below the change moves
# nothing: the build of the merge group holds that case (#7218).
# An edit below of the item's own lines changes its record at the
# base. A head that does not hold the group's base reads its change from
# their merge base (#6999).
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../cases/scratch.bash"
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
identity "$repo"
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

# A row that names the variant lands below the signed deletion. The change's
# words hold.
git -C "$repo" checkout --quiet landing
printf "INSERT INTO reader VALUES ('Gone');\n" > "$repo/ledger/readers.sql"
reader=$(commit reader)
git -C "$repo" checkout --quiet -b restacked-reader
git -C "$repo" cherry-pick --quiet "$signed" > /dev/null
restacked=$(git -C "$repo" rev-parse HEAD)
fork2=$(git -C "$repo" merge-base "$signed" "$reader")
got=$(cd "$repo" && moved "$fork2" "$signed" "$reader" "$restacked" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#6852: a row below that names the item moves no word of the change" "$got"

# A Rust source that names the variant lands below the signed deletion. It
# joins the readers of the item at the base, and it moves no word of the
# change: the build of the merge group refuses a true reader (#7218).
git -C "$repo" checkout --quiet landing
printf 'pub fn late() -> E { E::Gone }\n' > "$repo/src/late.rs"
late=$(commit late)
git -C "$repo" checkout --quiet -b restacked-late
git -C "$repo" cherry-pick --quiet "$signed" > /dev/null
relanded=$(git -C "$repo" rev-parse HEAD)
fork3=$(git -C "$repo" merge-base "$signed" "$late")
got=$(cd "$repo" && moved "$fork3" "$signed" "$late" "$relanded" Gone | tr '\n' ' ')
[[ -z $got ]] || fail "#7218: a source below that names the item joins its readers and moves no word of the change" "$got"

# The readers of an item stay within the crates that can name it (#7125).
# The item lives in `gandr-item`. `gandr-user` names that package, and
# `gandr-far` names `gandr-user`. The name of `gandr-item-base` only starts
# with the item's package, and `gandr-other` names `gandr-item-base` alone.
# A landing below adds a file with `receive` to each crate but the item's,
# which gets one with `receiver`. It also adds `receive` to a README of
# `gandr-user`, to a ledger row and to the comment of a script.
crates_repo=$work/crates
git init --quiet --initial-branch landing "$crates_repo"
identity "$crates_repo"
manifest() {
  mkdir -p "$crates_repo/crates/$1/src"
  printf '[package]\nname = "gandr-%s"\n\n[dependencies]\n' "$1" > "$crates_repo/crates/$1/Cargo.toml"
  if [[ -n ${2:-} ]]; then printf '%s\n' "$2" >> "$crates_repo/crates/$1/Cargo.toml"; fi
}
manifest item
manifest user 'gandr-item = { path = "../item" }'
manifest far 'gandr-user.workspace = true'
manifest item-base
manifest other 'gandr-item-base = { path = "../item-base" }'
crates_commit() { git -C "$crates_repo" add -A && git -C "$crates_repo" commit --quiet --no-verify -m "$1" && git -C "$crates_repo" rev-parse HEAD; }
crates_commit manifests > /dev/null
mkdir -p "$crates_repo/ledger"
printf 'fn f(receiver: u8) {}\n' > "$crates_repo/crates/item/src/a.rs"
printf 'fn g() { receive() }\n' > "$crates_repo/crates/user/src/b.rs"
printf '// receive\n' > "$crates_repo/crates/far/src/c.rs"
printf 'fn receive() {}\n' > "$crates_repo/crates/item-base/src/d.rs"
printf 'fn receive() {}\n' > "$crates_repo/crates/other/src/e.rs"
printf "INSERT INTO reader VALUES ('receive');\n" > "$crates_repo/ledger/readers.sql"
printf 'receive\n' > "$crates_repo/crates/user/README.md"
mkdir -p "$crates_repo/.config"
printf '# so the receive process holds no worktree\n' > "$crates_repo/.config/held.bash"
crates_base=$(crates_commit readers)
got=$(cd "$crates_repo" && crates_naming "$crates_base" 'gandr_item::session::receive' | tr '\n' ' ')
[[ $got == 'crates/far crates/item crates/user ' ]] \
  || fail "#7125: the crates that can name an item are its own and each crate that names one of them, to a fixed point; a name that only starts with the package names another" "$got"
# The files of the landing that hold `receive`, within the reach of the
# item `$1`.
printf '%s\n' crates/item/src/a.rs crates/user/src/b.rs crates/far/src/c.rs crates/item-base/src/d.rs crates/other/src/e.rs \
  ledger/readers.sql crates/user/README.md .config/held.bash > "$work/crates-changed"
crates_named() {
  local -a sources=()
  mapfile -t sources < <(cd "$crates_repo" && reach "$crates_base" "$1")
  (cd "$crates_repo" && named "$crates_base" receive "$work/crates-changed" "${sources[@]}") | LC_ALL=C sort | tr '\n' ' '
}
got=$(crates_named 'gandr_item::session::Program::<'"'"'arena>::receive')
[[ $got == 'crates/far/src/c.rs crates/item/src/a.rs crates/user/src/b.rs ' ]] \
  || fail "#7164: a file names an item as a Rust source of a crate that can name it; a README, a ledger row and a script name none" "$got"
got=$(crates_named 'gandr_item::session::tests::receive')
[[ $got == 'crates/item/src/a.rs ' ]] \
  || fail "#7125: an item of a test module is named in its own crate alone" "$got"
got=$(crates_named 'gandr_gone::receive')
[[ $got == 'crates/far/src/c.rs crates/item-base/src/d.rs crates/item/src/a.rs crates/other/src/e.rs crates/user/src/b.rs ' ]] \
  || fail "#7164: an item whose crate the base lacks is named in the Rust sources of every crate" "$got"

# A reader is a Rust source that the item's visibility lets name it (#7209).
# `gandr-item` holds the module `net::session`, `gandr-user` names
# `gandr-item`, and `gandr-lone` names nothing. `gandr-pathy` places a module
# by a `#[path]` attribute. Each record names a line of `session.rs` with
# one visibility, and the item's last segment is `receive` in each. A
# landing below adds `receive` to a file of each module and crate, and to a
# ledger row.
vis_repo=$work/visibility
git init --quiet --initial-branch landing "$vis_repo"
identity "$vis_repo"
vis_crate() {
  mkdir -p "$vis_repo/crates/$1/src"
  printf '[package]\nname = "gandr-%s"\n\n[dependencies]\n%s\n' "$1" "${2:-}" > "$vis_repo/crates/$1/Cargo.toml"
}
vis_crate item
vis_crate user 'gandr-item = { path = "../item" }'
vis_crate lone
vis_crate pathy
mkdir -p "$vis_repo/crates/item/src/net" "$vis_repo/ledger"
printf 'pub mod net;\nmod other;\n' > "$vis_repo/crates/item/src/lib.rs"
printf 'pub mod session;\n' > "$vis_repo/crates/item/src/net.rs"
printf 'fn other() {}\n' > "$vis_repo/crates/item/src/other.rs"
cat > "$vis_repo/crates/item/src/net/session.rs" << 'EOF'
pub fn exported_one() {}
pub(crate) fn crate_one() {}
pub(super) fn super_one() {}
fn private_one() {}
/// A private function under an attribute of three lines.
#[cfg_attr(
    test,
    allow(dead_code)
)]
fn attributed() {}
enum Kind {
    Receive,
}
pub struct Thing;
impl Clone for Thing {
    fn clone(&self) -> Self { Thing }
}
impl Thing {
    fn inherent(&self) {}
}
make_receive! {}
EOF
printf '#[path = "sub/other.rs"]\nmod o;\nmod s;\n' > "$vis_repo/crates/pathy/src/lib.rs"
printf 'fn hidden() {}\n' > "$vis_repo/crates/pathy/src/s.rs"
vis_commit() { git -C "$vis_repo" add -A && git -C "$vis_repo" commit --quiet --no-verify -m "$1" && git -C "$vis_repo" rev-parse HEAD; }
vis_commit visibility > /dev/null
mkdir -p "$vis_repo/crates/item/src/net/session" "$vis_repo/crates/user/src" "$vis_repo/crates/lone/src" "$vis_repo/crates/pathy/src/sub"
for file in crates/item/src/net.rs crates/item/src/other.rs crates/item/src/net/session/inner.rs \
  crates/user/src/b.rs crates/lone/src/c.rs crates/pathy/src/sub/other.rs; do
  printf '// receive\n' >> "$vis_repo/$file"
done
printf "INSERT INTO purpose VALUES ('receive');\n" > "$vis_repo/ledger/purposes.sql"
vis_base=$(vis_commit receive)
# The record of a line of `session.rs`: `<start> <line> <kind> <exported>`.
vis_record() {
  jq -n -c '$ARGS.positional as [$start, $at, $kind, $public, $file]
    | {file: $file, start: ($start | tonumber), line: ($at | tonumber), kind: $kind, exported: ($public == "true")}' \
    --args "$1" "$2" "$3" "$4" "${5:-crates/item/src/net/session.rs}"
}
# The files of the landing that hold `receive`, in the reach of the record
# `$2` of the item `$1`, or of its package when `$2` is empty.
printf '%s\n' crates/item/src/net.rs crates/item/src/other.rs crates/item/src/net/session/inner.rs \
  crates/user/src/b.rs crates/lone/src/c.rs crates/pathy/src/sub/other.rs ledger/purposes.sql > "$work/vis-landed"
vis_named() {
  local -a sources=()
  mapfile -t sources < <(cd "$vis_repo" && reach "$vis_base" "$1" "$2")
  (cd "$vis_repo" && named "$vis_base" receive "$work/vis-landed" "${sources[@]}") | LC_ALL=C sort | tr '\n' ' '
}
vis_item=gandr_item::net::session::receive
vis_package='crates/item/src/net.rs crates/item/src/net/session/inner.rs crates/item/src/other.rs crates/user/src/b.rs '
vis_in_crate='crates/item/src/net.rs crates/item/src/net/session/inner.rs crates/item/src/other.rs '
vis_in_module='crates/item/src/net/session/inner.rs '
got=$(vis_named "$vis_item" "$(vis_record 1 1 fn true)")
[[ $got == "$vis_package" ]] || fail "#7209: an exported item is read in each crate that can name its package" "$got"
got=$(vis_named "$vis_item" "$(vis_record 2 2 fn false)")
[[ $got == "$vis_in_crate" ]] || fail "#7209: a pub(crate) item is read in its own crate alone" "$got"
got=$(vis_named "$vis_item" "$(vis_record 3 3 fn false)")
[[ $got == 'crates/item/src/net.rs crates/item/src/net/session/inner.rs ' ]] \
  || fail "#7209: a pub(super) item is read in its parent module's file and below it" "$got"
got=$(vis_named "$vis_item" "$(vis_record 4 4 fn false)")
[[ $got == "$vis_in_module" ]] || fail "#7209: a private item is read in its own module's file and below it" "$got"
got=$(vis_named "$vis_item" "$(vis_record 5 10 fn false)")
[[ $got == "$vis_in_module" ]] || fail "#7209: the visibility stands past the doc comment and an attribute of three lines" "$got"
got=$(vis_named "$vis_item" "$(vis_record 12 12 variant false)")
[[ $got == "$vis_in_module" ]] || fail "#7209: a variant of a private enum is read in the enum's module" "$got"
got=$(vis_named "$vis_item" "$(vis_record 16 16 assoc-fn false)")
[[ $got == "$vis_package" ]] || fail "#7209: an item of an impl of a trait has the trait's reach, the package's" "$got"
got=$(vis_named "$vis_item" "$(vis_record 19 19 assoc-fn false)")
[[ $got == "$vis_in_module" ]] || fail "#7209: a private item of an inherent impl is read in its module" "$got"
got=$(vis_named "$vis_item" "$(vis_record 21 21 fn false)")
[[ $got == "$vis_package" ]] || fail "#7209: a header that the reading does not know, as a macro's, keeps the package's reach" "$got"
got=$(vis_named "$vis_item" '')
[[ $got == "$vis_package" ]] || fail "#7209: an item with no record keeps the package's reach" "$got"
got=$(vis_named gandr_pathy::s::receive "$(vis_record 1 1 fn false crates/pathy/src/s.rs)")
[[ $got == 'crates/pathy/src/sub/other.rs ' ]] \
  || fail "#7209: a private item of a crate with a #[path] attribute is read in its whole crate" "$got"
printf '%s\n' ledger/purposes.sql crates/item/src/other.rs crates/item/src/net/session/inner.rs > "$work/vis-changed"
got=$(cd "$vis_repo" && mapfile -t sources < <(reach "$vis_base" "$vis_item" "$(vis_record 4 4 fn false)") \
  && named "$vis_base" receive "$work/vis-changed" "${sources[@]}" | LC_ALL=C sort | tr '\n' ' ')
[[ $got == "$vis_in_module" ]] || fail "#7209: a ledger row or a source outside the reach names no private item, so its words move nothing" "$got"
got=$(cd "$vis_repo" && named "$vis_base" receive "$work/vis-changed" | LC_ALL=C sort | tr '\n' ' ')
[[ $got == 'crates/item/src/net/session/inner.rs crates/item/src/other.rs ledger/purposes.sql ' ]] \
  || fail "#7209: with no reach, each file of the change that holds the word names the item" "$got"

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
identity "$origin"
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
identity "$served_origin"
git -C "$served_origin" config uploadpack.allowReachableSHA1InWant true
git -C "$served_origin" config uploadpack.allowFilter true
git -C "$served_origin" commit --quiet --no-verify --allow-empty -m root
git -C "$served_origin" checkout --quiet -b change
git -C "$served_origin" commit --quiet --no-verify --allow-empty -m pushed
pushed=$(git -C "$served_origin" rev-parse HEAD)
git -C "$served_origin" commit --quiet --no-verify --allow-empty -m 'pushed, then left behind'
left=$(git -C "$served_origin" rev-parse HEAD)
git clone --quiet "file://$served_origin" "$work/seat"
identity "$work/seat"
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
echo "deletes moved OK: a restack over rows that a landing adds keeps the sign-off; an edit of another cell of a line that names the item keeps it; a change to a word that names the item or a new file that names it moves it; a file of the change names an item as a Rust source that the item's visibility lets name it, and a row, a README or a script names none; an edit below of its own lines changes its record; a head that does not hold the group's base reads its change from their merge base; a shallow clone reads the fork of a signed commit on no branch; a signed commit counts only when origin serves it"
