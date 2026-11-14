#!/usr/bin/env bash
# Reads the account that a pull request body gives of what its change takes
# out of the tree (#6817), and prints each refusal of `deletes.jq`. The
# change runs from the commit `<base>` to `HEAD`.
#
# The check reads four kinds at the base and at the head:
#   - the compiler's items and the suite's tests, from the evidence records of
#     the packages that the change touches, at the base in a scratch worktree
#     and at the head in this one. A test is an item that a test unit holds
#     and its library unit does not;
#   - the rows of each table of `ledger/*.sql`, by primary key, and the lines
#     of `.config/dead-weight/kept.txt`;
#   - the files under `corpus/`, `docs/` and `ledger/`, and each crate's
#     `README.md`, by path.
# The records come from the merge base, never from an artifact, since a stale
# record set gives a wrong account (#6817). The cache of `records.bash` keys
# each package's records by each input that they read, and a `cargo dylint`
# run builds each package that it does not hold (#6823).
#
# The check computes the act of each item and test that leaves its place
# (`acts.bash`, #7058). One whose body stands at an item that the head adds
# is moved or renamed, and it needs no row and no sign-off. One whose body
# stands nowhere in the head keeps its row, and that row asks the
# architect's sign-off.
#
# With `--rows-only`, as in the merge queue, it reads no records and no
# Cargo metadata: it reads the body's rows and the architect's sign-offs, so
# a body edited or a head pushed past a sign-off is refused. `--head <rev>`
# names the head there, the pull request's own commit, so the changes of the
# groups ahead of it in the queue move no sign-off.
#
# The sign-offs are the comments of the issues that the body works. gh reads
# each issue's comments: one REST read for each page of 100 comments. The
# logins that sign, each with the heading its comment must hold, are the
# factory's state and not the tree's, so they live outside it (#6962), in
# `$XDG_CONFIG_HOME/gandr/architects.txt`: one login a line, then the heading
# if any, and `#` starts a comment line. A host without the file refuses.
#
# Usage: check.bash [--rows-only [--head <rev>]] [--title <title>] <body> <base>
# Exits 1 on a refusal and 2 on a failed read.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git rev-parse --show-toplevel)
mode=full
title=
head=HEAD
while [[ ${1:-} == --* ]]; do
  case $1 in
    --rows-only) mode=rows; shift ;;
    --head) head=${2:?--head takes a revision}; shift 2 ;;
    --title) title=${2:?--title takes a title}; shift 2 ;;
    *) echo "check.bash: unknown flag $1" >&2; exit 2 ;;
  esac
done
[[ $mode == rows || $head == HEAD ]] || { echo "check.bash: --head reads the rows alone; the records read the work at HEAD" >&2; exit 2; }
body=${1:?usage: check.bash [--rows-only [--head <rev>]] [--title <title>] <body> <base>}
base=$(git rev-parse --verify --quiet "${2:?usage: check.bash [--rows-only [--head <rev>]] [--title <title>] <body> <base>}^{commit}") \
  || { echo "check:deletes: $2 is no commit" >&2; exit 2; }
head=$(git rev-parse --verify --quiet "$head^{commit}") || { echo "check:deletes: the head is no commit" >&2; exit 2; }
architects="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/architects.txt"
[[ -f $architects ]] || {
  echo "check:deletes: no signers at $architects: write each login that signs a \`deleted\` row there, one a line, then the heading its comment must hold (#6962)" >&2
  exit 2
}
scratch=$(mktemp -d)
cleanup() {
  if [[ -d $scratch/base ]]; then git -C "$root" worktree remove --force "$scratch/base" > /dev/null 2>&1 || :; fi
  rm -rf "$scratch"
}
trap cleanup EXIT
source "$root/.config/gh/repo.bash"
source "$here/digests.bash"
source "$here/moved.bash"
repo=$(repo_name)
SECONDS=0

from=$(change_base "$base" "$head")
git diff --no-renames --name-only "$from" "$head" > "$scratch/changed"
lonely='[]'
if [[ $mode == full ]]; then
  metadata=$(cargo metadata --format-version 1 --no-deps --locked --manifest-path "$root/Cargo.toml")
  # Each workspace package: its name, its library name, its directory, the
  # packages that it names, and whether it holds a binary.
  packages=$(jq -c --arg root "$root/" '[.packages[] | .name as $name | {name,
    library: ([.targets[] | select(.kind | index("lib")) | .name] | first // $name | gsub("-"; "_")),
    dir: (.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml") | ltrimstr("crates/")),
    deps: [.dependencies[].name],
    binary: any(.targets[]; .kind | index("bin"))}]' <<< "$metadata")
  # A crate that no other crate names waits for its consumer. A crate with a
  # binary is its own consumer.
  lonely=$(jq -c '. as $all | [.[] | select(.binary | not) | .name as $n | select([$all[] | select(.name != $n) | .deps[] | select(. == $n)] | length == 0) | {library, dir}]' <<< "$packages")
fi

# The rows of the body, as the rule reads them: the items of the rows that
# ask the architect's sign-off (#7058).
jq -n -r -L "$root/.config/bodies" -L "$here" --rawfile body "$body" \
  'include "account"; $body | deletes_rows // [] | .[] | select(.act | IN("deleted", "merged", "narrowed")) | .item' > "$scratch/deleted" 2> /dev/null || : > "$scratch/deleted"
# The last segment of each such row's item: the word that names it.
segments=$(while IFS= read -r item; do
  [[ -n $item ]] || continue
  jq -n -c --arg item "$item" --arg segment "$(sed -E 's/.*:://; s/[<>]//g' <<< "$item")" '{($item): $segment}'
done < "$scratch/deleted" | jq -s -c 'add // {}')
mapfile -t named_by < <(jq -r '[.[]] | unique[]' <<< "$segments")

# The architect's sign-offs: each comment that says `signed` on an issue the
# body works, with the commit it names, the base that commit forks from, and
# for each item the files where the words that name it moved since
# (`moved.bash`, #6852, #7025).
mapfile -t issues < <(jq -Rrs -L "$root/.config/bodies" 'include "targets"; targets(working) | unique[]' "$body")
signoffs=$(for issue in "${issues[@]}"; do
  gh api --paginate "repos/$repo/issues/$issue/comments?per_page=100" \
    --jq '.[] | select(.body | test("\\bsigned\\b")) | {author: .user.login, body}' \
    || { echo "check:deletes: the comments of #$issue cannot be read" >&2; exit 2; }
done | jq -s -c . | jq -c '.[]' | while IFS= read -r comment; do
  # A word names the signed commit only when `origin` serves it, as the queue
  # reads it (#7012). For a commit that the clone holds, the check asks
  # `origin` from a scratch repository. A commit that the clone lacks, the
  # check fetches, and the fetch is the answer.
  sha=
  for word in $(jq -r '.body' <<< "$comment" | digests); do
    if full=$(git rev-parse --verify --quiet "$word^{commit}"); then
      served "$scratch/origin" "$full" || continue
    elif git fetch --quiet --depth=1 origin "$word" 2> /dev/null; then
      full=$(git rev-parse --verify --quiet "$word^{commit}") || continue
    else
      continue
    fi
    sha=$full
    break
  done
  # The fork of the signed commit with the base (`signed_fork`, #6920). The
  # merge queue's clone is shallow, so the check fetches the signed line and
  # deepens the base, each by 500 commits, once. A sign-off with no fork
  # binds neither half, and the rule reads it as stale with that cause.
  fork=
  if [[ -n $sha ]]; then
    fork=$(signed_fork "$sha" "$base") || fork=
  fi
  if [[ -n $fork ]]; then
    moved "$fork" "$sha" "$from" "$head" "${named_by[@]}" \
      | jq -R -s -c --argjson c "$comment" --arg sha "$sha" --arg fork "$fork" --argjson segments "$segments" \
        '[split("\n")[] | select(. != "") | split("\t") | {segment: .[0], file: .[1]}] as $moved
         | $c + {sha: $sha, fork: $fork, reshaped: [],
             changed: ($segments | map_values(. as $s | [$moved[] | select(.segment == $s) | .file]))}'
  else
    jq -c --arg sha "$sha" '. + {sha: (if $sha == "" then null else $sha end), fork: null, changed: null, reshaped: []}' <<< "$comment"
  fi
done | jq -s -c .)

left='[]' held='[]' tests='[]' features='{}'
if [[ $mode == full ]]; then
  # The packages whose files the change touches, each with its directory.
  touched=$(jq -R . "$scratch/changed" | jq -s -c --slurpfile packages <(printf '%s\n' "$packages") \
    '[.[] | select(startswith("crates/")) | split("/")[1]] | unique as $dirs | [$packages[0][] | select(.dir | IN($dirs[])) | {name, dir}]')
  # The evidence records of the touched packages at a tree: `$1` the tree,
  # `$2` the directory the records go to, `$3` the side. The run takes the
  # policy's configuration and denials from the tree's own `check:dylint`
  # (`policy.bash`), so it builds as the gate's run does (#6838). Each
  # package's records come from the cache of `records.bash` when its key
  # holds, and the rest build there (#6823). A package that the change adds
  # has no manifest at the base, so the base's run leaves it out and each of
  # its items reads as added.
  records() {
    local tree=$1 out=$2 side=$3 args=() name dir summary
    mkdir -p "$out"
    while IFS=$'\t' read -r name dir; do
      if [[ -f $tree/crates/$dir/Cargo.toml ]]; then args+=("$name=crates/$dir"); fi
    done < <(jq -r '.[] | [.name, .dir] | @tsv' <<< "$touched")
    (( ${#args[@]} )) || return 0
    summary=$("$here/records.bash" "$tree" "$root/target/deletes" "$out" "${args[@]}") || exit 2
    cached+="; the $side ${summary#*: }"
  }
  cached=
  if [[ $touched != '[]' ]]; then
    git -C "$root" worktree add --quiet --detach "$scratch/base" "$base"
    records "$scratch/base" "$scratch/records-base" base
    records "$root" "$scratch/records-head" head
  fi
  # Each side's items and tests: {id, kind, file, start, end}. A test is an
  # item of a test unit that the library unit of the same root lacks. Each
  # file is at its path in the tree, or null for a source that a build script
  # writes (`paths.jq`, #6844).
  inventory() {
    local dir=$1
    shopt -s nullglob
    local units=("$dir"/*.jsonl)
    shopt -u nullglob
    (( ${#units[@]} )) || { echo '[]'; return; }
    for unit in "${units[@]}"; do
      jq -s -c -L "$here" --arg unit "$(basename "$unit" .jsonl)" \
        'include "paths"; {root: ($unit | sub("\\.[a-z-]+$"; "")), kind: ($unit | capture("\\.(?<k>[a-z-]+)$").k),
          items: [.[] | select(.record == "item") | {id: .path, kind, file: (.file | tree_path), start, end, line, exported}]}' "$unit" \
        || return 2
    done | jq -s -c '(map(select(.kind != "test")) | map({key: .root, value: (reduce .items[].id as $id ({}; .[$id] = true))}) | from_entries) as $lib
      | [.[] | .root as $root | .kind as $kind | .items[]
          | . + {test: ($kind == "test" and .kind == "fn" and ($lib[$root][.id] | not))}]
      | unique_by(.id)'
  }
  # A record whose relative path leaves the tree is refused (`paths.jq`),
  # since no git read reaches it.
  for side in base head; do
    inventory "$scratch/records-$side" > "$scratch/items-$side.json" \
      || { echo "check:deletes: a record of the $side names a file that leaves the tree" >&2; exit 2; }
  done
  # The act of each item and test that leaves and whose body stands at an
  # item that the head adds (`acts.bash`, #7058).
  "$here/acts.bash" "$base" "$scratch/items-base.json" "$scratch/items-head.json" > "$scratch/acts.json"
  # The keys of each ledger table at a revision, as `<table>:<key>,<key>`.
  ledger_keys() {
    local rev=$1 file table
    while IFS= read -r file; do
      git show "$rev:$file" > "$scratch/ledger.sql"
      sqlite3 :memory: ".read $scratch/ledger.sql" "SELECT name FROM sqlite_master WHERE type = 'table'" | while IFS= read -r table; do
        local columns
        columns=$(sqlite3 :memory: ".read $scratch/ledger.sql" "SELECT group_concat(name, ' || '','' || ') FROM pragma_table_info('$table') WHERE pk > 0")
        [[ -n $columns ]] || columns=rowid
        sqlite3 :memory: ".read $scratch/ledger.sql" "SELECT '$table:' || $columns FROM $table"
      done
    done < <(git ls-tree --name-only "$rev" -- ledger/ | awk '/\.sql$/')
  }
  ledger_keys "$base" | sort -u > "$scratch/ledger-base"
  ledger_keys HEAD | sort -u > "$scratch/ledger-head"
  kept_lines() { git show "$1:.config/dead-weight/kept.txt" 2> /dev/null | awk -F'\t' '!/^[[:space:]]*(#|$)/ { print $1 }' | sort -u; }
  kept_lines "$base" > "$scratch/kept-base"
  kept_lines HEAD > "$scratch/kept-head"
  # `git ls-tree` takes no glob, so the crates' tree is read and each README
  # kept.
  watched() { git ls-tree -r --name-only "$1" -- corpus docs ledger crates | awk '!/^crates\// || /^crates\/[^\/]+\/README\.md$/' | sort -u; }
  watched "$base" > "$scratch/files-base"
  watched HEAD > "$scratch/files-head"
  # The pull request that adds each thing that leaves: an item by its own
  # lines, a ledger row and a kept line by their text, and a file by its first
  # commit (`origin.bash`, #7259).
  origin() { "$here/origin.bash" "$base" text "$2" "$1"; }
  added() { "$here/origin.bash" "$base" file "$1"; }
  # The items of the base that the head lacks, in one pass over an object
  # keyed by the head's ids (#7479): a scan of the head's list for each item
  # of the base took minutes. Each line carries the item's fields and its
  # JSON, so the loop starts no `jq` to split them.
  left=$({
    jq -r --slurpfile head "$scratch/items-head.json" '(reduce $head[0][].id as $id ({}; .[$id] = true)) as $h
      | .[] | select($h[.id] | not) | "\(.id)\t\(.file // "")\t\(.start // "")\t\(.end // "")\t\(tojson)"' "$scratch/items-base.json" \
      | while IFS=$'\t' read -r id file start end item; do
          if [[ $start =~ ^[0-9]+$ && $end =~ ^[0-9]+$ ]]; then
            found=$("$here/origin.bash" "$base" span "$file" "$start" "$end")
          else
            found=$(origin "$(sed -E 's/.*:://; s/[<>]//g' <<< "$id")" "$file")
          fi
          jq -c --argjson origin "$found" --slurpfile acts "$scratch/acts.json" \
            '{id, kind: (if .test then "test" else "item" end), names: [.id], file, origin: $origin, moved: ($acts[0][.id] // null)}' <<< "$item"
        done
    comm -23 "$scratch/ledger-base" "$scratch/ledger-head" | while IFS= read -r key; do
      table=${key%%:*}
      fields=${key#*:}
      file=$(git grep -l -F -e "INSERT INTO $table " "$base" -- 'ledger/*.sql' | awk 'NR == 1 { sub("^[^:]*:", ""); print }')
      second=$(awk -F, '{ print ($2 == "" ? $1 : $2) }' <<< "$fields")
      # A row of `purpose` names an item of a crate: `<crate>,<path>,<kind>`.
      names=$(jq -n -c --arg key "$key" --arg table "$table" --arg fields "$fields" \
        '[$key] + (if $table == "purpose" then ($fields | split(",")) as [$c, $p] | ["gandr_" + ($c | gsub("-"; "_")) + "::" + $p] else [] end)')
      jq -n -c --arg id "$key" --argjson names "$names" --arg file "$file" --argjson origin "$(origin "$second" "$file")" \
        '{id: $id, kind: "ledger", names: $names, file: $file, origin: $origin}'
    done
    comm -23 "$scratch/kept-base" "$scratch/kept-head" | while IFS= read -r path; do
      jq -n -c --arg id "kept.txt:$path" --arg path "$path" --argjson origin "$(origin "$path" .config/dead-weight/kept.txt)" \
        '{id: $id, kind: "kept", names: [$id, $path], file: ".config/dead-weight/kept.txt", origin: $origin}'
    done
    comm -23 "$scratch/files-base" "$scratch/files-head" | while IFS= read -r path; do
      jq -n -c --arg id "$path" --argjson origin "$(added "$path")" '{id: $id, kind: "file", names: [$id], file: $id, origin: $origin}'
    done
  } | jq -s -c .)
  held=$({ jq -r '.[].id' "$scratch/items-head.json"; cat "$scratch/ledger-head" "$scratch/files-head"; sed 's/^/kept.txt:/' "$scratch/kept-head"; } | jq -R . | jq -s -c 'unique')
  # Each test of both sides whose lines differ (`tests.bash`).
  tests=$("$here/tests.bash" "$base" "$scratch/items-base.json" "$scratch/items-head.json")
  # The lines of `## Provided features` of each crate that a left item lives
  # in, at the base and at the head: `deletes.jq` reads which items they name.
  features=$(jq -r '[.[] | select(.kind == "item") | .file // "" | select(test("^crates/[^/]+/")) | split("/")[1]] | unique[]' <<< "$left" | while IFS= read -r dir; do
    lines() { git show "$1:crates/$dir/README.md" 2> /dev/null | awk '/^## /{ on = ($0 == "## Provided features") ; next } on'; }
    jq -n -c --arg dir "$dir" --rawfile base <(lines "$base") --rawfile head <(lines HEAD) \
      '{($dir): {base: ($base | split("\n")), head: ($head | split("\n"))}}'
  done | jq -s -c 'add // {}')
fi

# The reach of each such row's item at the base (`reach`, #7209): the Rust
# sources that its visibility lets name it. A full run reads the visibility
# from the one record at the base that the item covers. The rows-only run
# has no records, so each item reaches its package.
declare -A reaches=()
while IFS= read -r item; do
  [[ $item == *::* ]] || continue
  record=
  if [[ -f $scratch/items-base.json ]]; then
    record=$(jq -c -L "$root/.config/bodies" -L "$here" --arg item "$item" \
      'include "account"; [.[] | select(.file != null and covers($item; {id, names: [.id]}))] | if length == 1 then .[0] else empty end' \
      "$scratch/items-base.json")
  fi
  reaches[$item]=$(reach "$base" "$item" "$record")
done < "$scratch/deleted"

# The files of the change that name each such row's item at the base, within
# the reach of an item of a crate (`named`, #7209).
files=$(jq -r 'to_entries[] | [.key, .value] | @tsv' <<< "$segments" | while IFS=$'\t' read -r item segment; do
  sources=()
  [[ -n ${reaches[$item]:-} ]] && mapfile -t sources <<< "${reaches[$item]}"
  mapfile -t names < <(named "$base" "$segment" "$scratch/changed" "${sources[@]}")
  jq -n -c --arg item "$item" '{($item): $ARGS.positional}' --args "${names[@]}"
done | jq -s -c 'add // {}')

# The item's half of each sign-off (#6852): the items whose record at the
# base changes below the signed commit. The read needs the base's records,
# so the merge queue's rows-only run binds the change's half alone. A source
# that joins an item's readers at the base binds nothing here: the build of
# the merge group refuses a source that names a removed item (#7218).
if [[ -f $scratch/items-base.json ]]; then
  signoffs=$(jq -c '.[]' <<< "$signoffs" | while IFS= read -r c; do
    fork=$(jq -r '.fork // empty' <<< "$c")
    if [[ -z $fork || $fork == "$(git rev-parse "$base")" ]]; then printf '%s\n' "$c"; continue; fi
    reshapes='[]'
    while IFS= read -r item; do
      [[ -n $item ]] || continue
      jq -e --arg item "$item" '.body | contains($item)' <<< "$c" > /dev/null || continue
      while IFS=$'\t' read -r file start end; do
        if reshaped "$fork" "$base" "$file" "$start" "$end"; then
          reshapes=$(jq -c --arg item "$item" '. + [$item] | unique' <<< "$reshapes")
          break
        fi
      done < <(jq -r -L "$root/.config/bodies" -L "$here" --arg item "$item" \
        'include "account"; .[] | select(.file != null and covers($item; {id, names: [.id]})) | [.file, .start, .end] | @tsv' "$scratch/items-base.json")
    done < "$scratch/deleted"
    jq -c --slurpfile r <(printf '%s' "$reshapes") '. + {reshaped: $r[0]}' <<< "$c"
  done | jq -s -c .)
fi

# The readings go to jq as files: the held set names each file of the corpus,
# past the kernel's limit for one argument.
for name in left held tests features lonely files signoffs; do printf '%s\n' "${!name}" > "$scratch/$name.json"; done
jq -Rn -c '[inputs | select(test("^[^#]")) | capture("^(?<login>\\S+)\\s*(?<heading>.*)$") | {(.login): .heading}] | add // {}' "$architects" > "$scratch/architects.json"
findings=$(jq -n -c --rawfile body "$body" --arg title "$title" --arg mode "$mode" \
  --slurpfile left "$scratch/left.json" --slurpfile held "$scratch/held.json" --slurpfile tests "$scratch/tests.json" \
  --slurpfile features "$scratch/features.json" --slurpfile lonely "$scratch/lonely.json" --slurpfile files "$scratch/files.json" \
  --slurpfile signoffs "$scratch/signoffs.json" --slurpfile architects "$scratch/architects.json" \
  '{body: $body, title: $title, mode: $mode, left: $left[0], held: $held[0], tests: $tests[0], features: $features[0],
    lonely: $lonely[0], files: $files[0], signoffs: $signoffs[0], architects: $architects[0]}' \
  | jq -r -L "$root/.config/bodies" -L "$here" -f "$here/deletes.jq")
if [[ -n $findings ]]; then
  echo "$findings" >&2
  echo "check:deletes: account for each thing above in the body's \`## Deletes\` (#6817), then run the task again; ${SECONDS}s" >&2
  exit 1
fi
echo "check:deletes OK: $(jq length <<< "$left") things leave the tree, $(jq '[.[] | select(.moved != null)] | length' <<< "$left") of them moved or renamed with the same body and each other with its row${cached:-}; ${SECONDS}s"
