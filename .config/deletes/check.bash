#!/usr/bin/env bash
# Reads the account that a pull request body gives of what its change takes
# out of the tree (#6817), and prints each refusal of `deletes.jq`. The
# change runs from the commit `<base>` to `HEAD`.
#
# The check reads four kinds at the base and at the head:
#   - the compiler's items and the suite's tests, from the evidence records of
#     a `cargo dylint` run over the packages that the change touches, at the
#     base in a scratch worktree and at the head in this one. A test is an
#     item that a test unit holds and its library unit does not;
#   - the rows of each table of `ledger/*.sql`, by primary key, and the lines
#     of `.config/dead-weight/kept.txt`;
#   - the files under `corpus/`, `docs/` and `ledger/`, and each crate's
#     `README.md`, by path.
# The records come from the merge base, never from an artifact, since a stale
# record set gives a wrong account (#6817).
#
# With `--rows-only`, as in the merge queue, it reads no records and no
# Cargo metadata: it reads the body's rows and the architect's sign-offs, so
# a body edited or a head pushed past a sign-off is refused. `--head <rev>`
# names the head there, the pull request's own commit, so the changes of the
# groups ahead of it in the queue move no sign-off.
#
# The sign-offs are the comments of the issues that the body works. gh reads
# each issue's comments: one REST read for each page of 100 comments.
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
scratch=$(mktemp -d)
cleanup() {
  if [[ -d $scratch/base ]]; then git -C "$root" worktree remove --force "$scratch/base" > /dev/null 2>&1 || :; fi
  rm -rf "$scratch"
}
trap cleanup EXIT
source "$root/.config/gh/repo.bash"
source "$here/digests.bash"
repo=$(repo_name)
SECONDS=0

git diff --no-renames --name-only "$base" "$head" > "$scratch/changed"
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

# The rows of the body, as the rule reads them.
jq -n -r -L "$root/.config/claims" -L "$here" --rawfile body "$body" \
  'include "account"; $body | deletes_rows // [] | .[] | select(.act == "deleted") | .item' > "$scratch/deleted" 2> /dev/null || : > "$scratch/deleted"
# The files of the change that name each `deleted` row's item at the base.
files=$(while IFS= read -r item; do
  [[ -n $item ]] || continue
  segment=$(sed -E 's/.*:://; s/[<>]//g' <<< "$item")
  mapfile -t named < <(git grep -l -F -e "$segment" "$base" -- $(< "$scratch/changed") 2> /dev/null | sed "s|^$base:||" || :)
  jq -n -c --arg item "$item" '{($item): $ARGS.positional}' --args "${named[@]}"
done < "$scratch/deleted" | jq -s -c 'add // {}')

# The architect's sign-offs: each comment that says `signed` on an issue the
# body works, with the commit it names and the files changed since.
mapfile -t issues < <(jq -Rrs -L "$root/.config/claims" 'include "targets"; targets(working) | unique[]' "$body")
signoffs=$(for issue in "${issues[@]}"; do
  gh api --paginate "repos/$repo/issues/$issue/comments?per_page=100" \
    --jq '.[] | select(.body | test("\\bsigned\\b")) | {author: .user.login, body}' \
    || { echo "check:deletes: the comments of #$issue cannot be read" >&2; exit 2; }
done | jq -s -c . | jq -c '.[]' | while IFS= read -r comment; do
  sha=
  for word in $(jq -r '.body' <<< "$comment" | digests); do
    if git cat-file -e "$word^{commit}" 2> /dev/null || { git fetch --quiet --depth=1 origin "$word" 2> /dev/null && git cat-file -e "$word^{commit}" 2> /dev/null; }; then
      sha=$(git rev-parse "$word^{commit}")
      break
    fi
  done
  if [[ -n $sha ]]; then
    git diff --no-renames --name-only "$sha" "$head" | jq -R . | jq -s -c --argjson c "$comment" --arg sha "$sha" '$c + {sha: $sha, changed: .}'
  else
    jq -c '. + {sha: null, changed: null}' <<< "$comment"
  fi
done | jq -s -c .)

left='[]' held='[]' tests='[]' readme='[]'
if [[ $mode == full ]]; then
  # The packages whose files the change touches.
  touched=$(jq -R . "$scratch/changed" | jq -s -c --argjson packages "$packages" \
    '[.[] | select(startswith("crates/")) | split("/")[1]] | unique as $dirs | [$packages[] | select(.dir | IN($dirs[])) | .name]')
  # The evidence records of the touched packages at a tree: `$1` the tree,
  # `$2` the directory the records go to. The run takes the policy's
  # configuration and denials from the tree's own `check:dylint`
  # (`policy.bash`), so it builds as the gate's run does (#6838).
  records() {
    local tree=$1 out=$2 args=() config flags
    mkdir -p "$out"
    mapfile -t names < <(jq -r '.[]' <<< "$touched")
    (( ${#names[@]} )) || return 0
    for name in "${names[@]}"; do args+=(-p "$name"); done
    config=$("$here/policy.bash" "$tree" "$out")
    flags=$("$here/policy.bash" --flags "$tree" "$out")
    (cd "$tree" \
      && CARGO_INCREMENTAL=0 CARGO_TARGET_DIR="$root/target/deletes" \
        CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=dylint-link CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=dylint-link \
        CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER=dylint-link CARGO_TARGET_X86_64_APPLE_DARWIN_LINKER=dylint-link \
        CARGO_ENCODED_RUSTFLAGS=$'--cfg=quenchant_compiler_policy\x1f-Zalways-encode-mir\x1f-Zinline-mir=no' \
        DYLINT_TOML=$config DYLINT_RUSTFLAGS=$flags \
        cargo dylint --lib quenchant_dylints -- "${args[@]}" --all-targets --locked --quiet) > "$scratch/dylint.log" 2>&1 \
      || { echo "check:deletes: the records of $tree do not build:" >&2; tail -n 20 "$scratch/dylint.log" >&2; exit 2; }
  }
  if [[ $touched != '[]' ]]; then
    git -C "$root" worktree add --quiet --detach "$scratch/base" "$base"
    records "$scratch/base" "$scratch/records-base"
    records "$root" "$scratch/records-head"
  fi
  # Each side's items and tests: {id, kind, file, start, end}. A test is an
  # item of a test unit that the library unit of the same root lacks.
  inventory() {
    local dir=$1
    shopt -s nullglob
    local units=("$dir"/*.jsonl)
    shopt -u nullglob
    (( ${#units[@]} )) || { echo '[]'; return; }
    for unit in "${units[@]}"; do
      jq -s -c --arg unit "$(basename "$unit" .jsonl)" \
        '{root: ($unit | sub("\\.[a-z-]+$"; "")), kind: ($unit | capture("\\.(?<k>[a-z-]+)$").k),
          items: [.[] | select(.record == "item") | {id: .path, kind, file, start, end}]}' "$unit"
    done | jq -s -c '(map(select(.kind != "test")) | map({key: .root, value: [.items[].id]}) | from_entries) as $lib
      | [.[] | .root as $root | .kind as $kind | .items[]
          | . + {test: ($kind == "test" and .kind == "fn" and (.id | IN(($lib[$root] // [])[]) | not))}]
      | unique_by(.id)'
  }
  inventory "$scratch/records-base" > "$scratch/items-base.json"
  inventory "$scratch/records-head" > "$scratch/items-head.json"
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
  # The pull request of the commit that adds a text to a file at the base:
  # the oldest commit whose change adds or removes the text, and the number
  # its subject ends with.
  origin() {
    local text=$1 file=$2 subject
    subject=$(git log --reverse --format=%s -S"$text" "$base" -- "$file" 2> /dev/null | awk 'NR == 1')
    [[ $subject =~ \(#([0-9]+)\)$ ]] && echo "${BASH_REMATCH[1]}" || echo null
  }
  added() {
    local subject
    subject=$(git log --diff-filter=A --format=%s "$base" -- "$1" 2> /dev/null | awk 'END { print }')
    [[ $subject =~ \(#([0-9]+)\)$ ]] && echo "${BASH_REMATCH[1]}" || echo null
  }
  left=$({
    jq -c --slurpfile head "$scratch/items-head.json" '($head[0] | map(.id)) as $h | .[] | select(.id | IN($h[]) | not)' "$scratch/items-base.json" \
      | while IFS= read -r item; do
          id=$(jq -r .id <<< "$item")
          file=$(jq -r .file <<< "$item")
          segment=$(sed -E 's/.*:://; s/[<>]//g' <<< "$id")
          jq -c --argjson origin "$(origin "$segment" "$file")" '{id, kind: (if .test then "test" else "item" end), names: [.id], file, origin: $origin}' <<< "$item"
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
  # Each test of both sides whose lines differ.
  tests=$(jq -c --slurpfile head "$scratch/items-head.json" \
    '($head[0] | map(select(.test)) | map({key: .id, value: .}) | from_entries) as $h | .[] | select(.test) | select($h[.id] != null) | [., $h[.id]]' "$scratch/items-base.json" \
    | while IFS= read -r pair; do
        old=$(jq -r '.[0] | "\(.file) \(.start) \(.end)"' <<< "$pair")
        new=$(jq -r '.[1] | "\(.file) \(.start) \(.end)"' <<< "$pair")
        read -r ofile ostart oend <<< "$old"
        read -r nfile nstart nend <<< "$new"
        if [[ $(git show "$base:$ofile" | sed -n "${ostart},${oend}p") != "$(sed -n "${nstart},${nend}p" "$root/$nfile")" ]]; then
          jq -c '.[0] | {id, name: (.id | sub("^.*::"; ""))}' <<< "$pair"
        fi
      done | jq -s -c .)
  # Each left item that the crate's `## Provided features` names on a line
  # that the head keeps: by its own segment or its owner's, in backquotes or
  # as the words of its name.
  readme=$(jq -c '.[] | select(.kind == "item")' <<< "$left" | while IFS= read -r item; do
    file=$(jq -r .file <<< "$item")
    [[ $file == crates/*/* ]] || continue
    readme_file="crates/$(cut -d/ -f2 <<< "$file")/README.md"
    features() { git show "$1:$readme_file" 2> /dev/null | awk '/^## /{ on = ($0 == "## Provided features") ; next } on'; }
    features "$base" > "$scratch/features-base"
    features HEAD > "$scratch/features-head"
    jq -r '.id | split("::") | map(gsub("<.*$"; "")) | .[-2:][] | select(test("^[A-Za-z_][A-Za-z0-9_]*$"))' <<< "$item" | while IFS= read -r name; do
      words=$(sed -E 's/([a-z0-9])([A-Z])/\1 \2/g' <<< "$name" | tr '[:upper:]' '[:lower:]')
      while IFS= read -r line; do
        lower=$(tr '[:upper:]' '[:lower:]' <<< "$line")
        if [[ $line == *"\`$name\`"* || ( $words == *" "* && $lower == *"$words"* ) ]] && grep -qxF -e "$line" "$scratch/features-head"; then
          jq -r .id <<< "$item"
          break 2
        fi
      done < "$scratch/features-base"
    done
  done | jq -R . | jq -s -c 'unique')
fi

# The readings go to jq as files: the held set names each file of the corpus,
# past the kernel's limit for one argument.
for name in left held tests readme lonely files signoffs; do printf '%s\n' "${!name}" > "$scratch/$name.json"; done
jq -Rn -c '[inputs | select(test("^[^#]")) | capture("^(?<login>\\S+)\\s*(?<heading>.*)$") | {(.login): .heading}] | add // {}' "$here/architects.txt" > "$scratch/architects.json"
findings=$(jq -n -c --rawfile body "$body" --arg title "$title" --arg mode "$mode" \
  --slurpfile left "$scratch/left.json" --slurpfile held "$scratch/held.json" --slurpfile tests "$scratch/tests.json" \
  --slurpfile readme "$scratch/readme.json" --slurpfile lonely "$scratch/lonely.json" --slurpfile files "$scratch/files.json" \
  --slurpfile signoffs "$scratch/signoffs.json" --slurpfile architects "$scratch/architects.json" \
  '{body: $body, title: $title, mode: $mode, left: $left[0], held: $held[0], tests: $tests[0], readme: $readme[0],
    lonely: $lonely[0], files: $files[0], signoffs: $signoffs[0], architects: $architects[0]}' \
  | jq -r -L "$root/.config/claims" -L "$here" -f "$here/deletes.jq")
if [[ -n $findings ]]; then
  echo "$findings" >&2
  echo "check:deletes: account for each thing above in the body's \`## Deletes\` (#6817), then run the task again; ${SECONDS}s" >&2
  exit 1
fi
echo "check:deletes OK: $(jq length <<< "$left") things leave the tree, each with its row; ${SECONDS}s"
