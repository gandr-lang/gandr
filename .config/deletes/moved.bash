# shellcheck shell=bash
# The files where the words that name an item moved since a sign-off (#6852,
# #7025). `moved <fork> <sha> <from> <head> <segment>…` prints `<segment>`,
# a tab and a file, one for each line, for each file where the words that
# hold `<segment>` differ between the change at the sign-off and the change
# now. The change at the sign-off runs from `<fork>`, the merge base of
# `<sha>` with the base, to `<sha>`. The change now runs from `<from>` to
# `<head>`, where `<from>` is `change_base`'s.
#
# The diff has no context lines, so a line number moves nothing, and the
# rows that a landing below adds to a shared file move no word. A restack
# over such a landing then keeps the sign-off, as the restack of pull
# request 6848 over the purpose rows of `ledger/purposes.sql` did not. The
# check reads, in each added or removed line, only the words that hold the
# segment: runs of characters other than space, quote, comma and
# parenthesis. A common segment as `ledger` names 39 of the 45 files of
# pull request 7017. An edit of another cell of such a line, as its `since`,
# moves nothing. A word that the change adds, drops or renames moves the
# sign-off. A sign-off with no fork in the clone binds neither half, and
# `check.bash` reads it as stale.
moved() {
  local fork=$1 sha=$2 from=$3 head=$4
  shift 4
  words() {
    local a=$1 b=$2
    shift 2
    git diff --no-renames --unified=0 "$a" "$b" \
      | MOVED_SEGMENTS=$(printf '%s\n' "$@") awk -v q="'" '
        BEGIN { n = split(ENVIRON["MOVED_SEGMENTS"], segment, "\n"); gap = "[[:space:]" q "\",()]+" }
        /^diff --git / { file = $0; sub(/^diff --git a\//, "", file); sub(/ b\/.*$/, "", file); body = 0; next }
        /^@@/ { body = 1; next }
        !body || !/^[-+]/ { next }
        {
          sign = substr($0, 1, 1)
          m = split(substr($0, 2), word, gap)
          for (i = 1; i <= m; i++) for (j = 1; j <= n; j++)
            if (segment[j] != "" && index(word[i], segment[j])) print segment[j] "\t" file "\t" sign word[i]
        }' | LC_ALL=C sort
  }
  LC_ALL=C comm -3 <(words "$fork" "$sha" "$@") <(words "$from" "$head" "$@") \
    | awk -F'\t' '{ if ($1 == "") print $2 "\t" $3; else print $1 "\t" $2 }' | LC_ALL=C sort -u
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

# Whether `origin` serves a signed commit (#7012). `served <scratch> <sha>`
# succeeds when a fetch of the full name `<sha>` from `origin` reaches it, as
# the merge queue's clone reads a sign-off. A seat's clone holds each commit
# that the seat makes, pushed or not. When the clone holds the commit, `git
# fetch` asks `origin` nothing, so the read goes into `<scratch>`, an empty
# repository that holds no commit. The fetch takes the commit object alone,
# at depth 1 and with no tree. The scratch repository takes the clone's
# extra HTTP headers, so a clone that `actions/checkout` authorises reads as
# it does.
served() {
  local scratch=$1 sha=$2 key value url
  local -a config=()
  [[ -d $scratch/.git ]] || git init --quiet "$scratch"
  while read -r key value; do
    config+=(-c "$key=$value")
  done < <(git config --get-regexp '^http\..*\.extraheader$' 2> /dev/null || :)
  url=$(git remote get-url origin) || return 1
  git -C "$scratch" "${config[@]}" fetch --quiet --depth=1 --filter=tree:0 "$url" "$sha" 2> /dev/null
}

# The item's half of a sign-off (#6852). A restack can keep the change's own
# patch and still change what the deletion means. The architect reads the
# item as it stands at the base, with its readers, so the check binds both.
#
# `crates_naming <base> <item>` prints the directory of each crate at
# `<base>` that can name `<item>`, one for each line (#7125). The first
# segment of the item's path is its crate's library, `gandr_core_checker`
# for the package `gandr-core-checker`. A crate can name the item when it is
# the item's crate, or when its manifest names a crate that can, to a fixed
# point. A manifest names a package by its whole name, so `gandr-core-checker`
# names no `gandr-core-checker-base`. An item with `tests` among its segments
# is seen by its own crate alone. An item with no crate segment, or whose
# crate the base lacks, prints nothing, and every crate can read it.
crates_naming() {
  local base=$1 item=$2
  [[ $item == *::* ]] || return 0
  local package=${item%%::*}
  package=${package//_/-}
  local alone=0
  [[ "::$item::" == *::tests::* ]] && alone=1
  git grep -I -e '' "$base" -- 'crates/*/Cargo.toml' 2> /dev/null | awk -v want="$package" -v alone="$alone" '
    match($0, /^[^:]*:crates\/[^\/]+\/Cargo\.toml:/) {
      dir = substr($0, 1, RLENGTH - 1)
      text = substr($0, RLENGTH + 1)
      sub(/^[^:]*:crates\//, "", dir)
      sub(/\/Cargo\.toml$/, "", dir)
      if (!(dir in package) && text ~ /^name = "/) {
        name = text
        sub(/^name = "/, "", name)
        sub(/".*/, "", name)
        package[dir] = name
        dir_of[name] = dir
      } else {
        body[dir] = body[dir] "\n" text
      }
    }
    END {
      if (!(want in dir_of)) exit
      naming[want] = 1
      grew = !alone
      while (grew) {
        grew = 0
        for (dir in package) {
          if (package[dir] in naming) continue
          for (name in naming) {
            if (match(body[dir], "(^|[^A-Za-z0-9_-])" name "([^A-Za-z0-9_-]|$)")) {
              naming[package[dir]] = 1
              grew = 1
              break
            }
          }
        }
      }
      for (name in naming) print "crates/" dir_of[name]
    }' | sort
}

# `joined <fork> <base> <item>` prints each file at `<base>` that names
# `<item>` and that names it nowhere at `<fork>`, one for each line. Such a
# file is a new reader of the item. A reader is a Rust source of a crate that
# can name the item (`crates_naming`), or of any crate when none is known,
# and no other file (#7164): a script, a ledger row or a README is no reader.
# A Rust source names the item by the whole word of its last segment (#7125).
joined() {
  local fork=$1 base=$2 item=$3 name crate crates
  name=$(sed -E 's/.*:://; s/[<>]//g' <<< "$item")
  mapfile -t crates < <(crates_naming "$base" "$item")
  local -a sources=()
  if (( ${#crates[@]} == 0 )); then
    sources=(':(glob)crates/**/*.rs')
  else
    for crate in "${crates[@]}"; do sources+=(":(glob)$crate/**/*.rs"); done
  fi
  joined_readers() {
    git grep -l -w -F -e "$name" "$1" -- "${sources[@]}" 2> /dev/null | sed "s|^$1:||" | sort -u
  }
  comm -13 <(joined_readers "$fork") <(joined_readers "$base")
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
