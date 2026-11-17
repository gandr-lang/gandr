#!/usr/bin/env bash
# The codemod of the region's adoption: the ids of an arena take the region's
# brand `'r`, and so does each type, impl and function that holds them. The
# task `codemod:region` runs it over the crates of a wave and the crates above
# them. The compiler's errors that stay are the wave's second phase.
#
# A rule matches a name and does not resolve an import, and two crates may
# define types of the same name. So the codemod reads each file's imports.
# `imports_granularity = "Item"` keeps one item to each `use`, so a line
# match reads them. A provider is a pair of a crate and a name: an id of the
# arena, a holder that takes the brand, or a re-export of either. In each
# file, the names that stand for a provider are the file's own definitions,
# each `use` of a provider under its local name, and each provider of a crate
# that the file imports by a glob.
#
# One pass of `awk` reads the providers and the names of each file. It writes
# one rule set: each rule of `.config/ast-grep/region/templates` for each
# name, with the files where the name stands for a provider as the rule's
# `files`. So one run of `ast-grep` parses each file once and applies each
# rule only where its name is a provider.
#
# The rules run in four phases, and each runs until a pass changes nothing:
# 1. the types: each holder takes the brand, then the providers are read
#    again, then each file's uses take it. The phase ends when neither the
#    providers nor a file change.
# 2. the impls of the holders.
# 3. the functions whose signatures name the brand. A method of an impl that
#    takes the brand reads the impl's, so this phase runs after the impls.
# 4. with `--arena`, the rollbacks of the arena that it names, in the files
#    where that name stands for the seed crate's arena: each rollback in the
#    one-exit shape takes a fork of one child (#7558). The rules count the
#    rollbacks that they rewrite, and they list each one that stays for the
#    hand by its file and line.
#
# A dry run clones the paths into a scratch directory and runs there. It
# prints the same rounds and counts, and it leaves the tree as it is. So a
# report can hold the rules current against each landing.
#
# Usage: codemod-region.bash [--dry-run] [--path <path>]... [--arena <name>]
#   <crate> <name>...
# The crate and the names are the seed providers, and the paths default to
# `crates`. The task prints each round and the brands it adds, by crate.
set -euo pipefail
export LC_ALL=C

dry_run=0
arena=
paths=()
while (( $# > 0 )); do
  case $1 in
    --dry-run) dry_run=1 && shift ;;
    --path)
      (( $# >= 2 )) || { echo 'codemod-region: --path takes a path' >&2; exit 2; }
      paths+=("$2")
      shift 2
      ;;
    --arena)
      (( $# >= 2 )) || { echo 'codemod-region: --arena takes a name' >&2; exit 2; }
      arena=$2
      shift 2
      ;;
    *) break ;;
  esac
done
(( $# >= 2 )) || { echo 'codemod-region: name the seed crate and its ids' >&2; exit 2; }
seed_crate=$1
shift
seed_names="$*"
(( ${#paths[@]} > 0 )) || paths=(crates)

region=$PWD/.config/ast-grep/region
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
# `ast-grep` reads a rule's `files` from the directory that holds the files
# it scans, unless they lie under its configuration's directory. So the rule
# set and the clone of a dry run are two directories apart.
rule_set=$scratch/rules
mkdir -p "$rule_set/rules"
printf 'ruleDirs:\n  - rules\n' > "$rule_set/sgconfig.yml"
# The rules of the rollbacks, which the last round writes: a configuration of
# their own, since they run once after the phases of the brand.
rollback_set=$scratch/rollbacks
mkdir -p "$rollback_set/rules"
printf 'ruleDirs:\n  - rules\n' > "$rollback_set/sgconfig.yml"

# A dry run works in a clone of the paths, with the root's ignore file and a
# repository of its own, so `rg` and `ast-grep` skip what the tree ignores.
if (( dry_run )); then
  copy=$scratch/tree
  for path in "${paths[@]}"; do
    mkdir -p "$copy/$(dirname "$path")"
    if [[ $(uname -s) == Darwin ]]; then
      cp -c -R -p "$path" "$copy/$path"
    else
      cp -a --reflink=auto "$path" "$copy/$path"
    fi
  done
  cp .gitignore "$copy/.gitignore"
  git init -q "$copy"
  cd "$copy"
fi

# The count of brands in each crate: each `'r` and each `'_`.
brands() {
  rg -c "'r\\b|'_" --type rust "${paths[@]}" \
    | awk -F: '{ split($1, part, "/"); count[part[2]] += $NF } END { for (crate in count) print crate, count[crate] }' \
    | sort
}

# Apply the rules of the configuration `$1` whose ids match `$2` to the
# paths, until a pass changes nothing. Succeed when a pass changed a file.
fixpoint() {
  local config=$1 filter=$2 output changed=1
  while :; do
    output=$(ast-grep scan --config "$config" --filter "$filter" --update-all "${paths[@]}" 2>&1)
    [[ ${output,,} != *error* ]] || { printf '%s\n' "$output" >&2; exit 1; }
    [[ $output =~ Applied\ ([0-9]+) ]] && (( BASH_REMATCH[1] > 0 )) || break
    changed=0
  done
  return "$changed"
}

# Read the holders and the `use` lines, and write the rule set of the uses.
# The first input holds `<file>\t<name>` for each holder that a file defines.
# The second holds `<file>:<line>` for each `use` line. The templates come
# through the environment, so `awk` reads their backslashes as they are.
# The script prints the rule set, and a line of counts to stderr.
names_awk='
function library(file,  part) {
  part = file
  sub(/^crates\//, "", part)
  sub(/\/.*/, "", part)
  gsub(/-/, "_", part)
  return "gandr_" part
}
function directory_of(file,  part) {
  part = file
  sub(/^crates\//, "", part)
  sub(/\/.*/, "", part)
  return part
}
function fill(template, id, names, path, files,  text) {
  text = template
  gsub(/__ID__/, id, text)
  gsub(/__NAMES__/, names, text)
  gsub(/__PATH__/, path, text)
  gsub(/__FILES__/, files, text)
  return text
}
function emit(text) {
  printf "%s%s\n", (emitted++ ? "---\n" : ""), text
}
BEGIN {
  FS = "\t"
  count = split(ENVIRON["SEED_NAMES"], seed, " ")
  for (i = 1; i <= count; i++) provider[ENVIRON["SEED_CRATE"] SUBSEP seed[i]] = 1
  if (ENVIRON["ARENA"] != "") arena[ENVIRON["SEED_CRATE"] SUBSEP ENVIRON["ARENA"]] = 1
}
FILENAME == ARGV[1] {
  provider[library($1) SUBSEP $2] = 1
  directory[library($1)] = directory_of($1)
  own[++owned] = $1 SUBSEP $2
  next
}
{
  split_at = index($0, ":")
  file = substr($0, 1, split_at - 1)
  line = substr($0, split_at + 1)
  directory[library(file)] = directory_of(file)
  sub(/^[ \t]*/, "", line)
  public = (line ~ /^pub[( \t]/)
  sub(/^pub(\([^)]*\))?[ \t]+/, "", line)
  if (line !~ /^use[ \t]/ || line ~ /[{}]/ || line !~ /;[ \t]*$/) next
  sub(/^use[ \t]+/, "", line)
  sub(/[ \t]*;[ \t]*$/, "", line)
  alias = ""
  if (match(line, /[ \t]+as[ \t]+/)) {
    alias = substr(line, RSTART + RLENGTH)
    line = substr(line, 1, RSTART - 1)
  }
  sub(/^::/, "", line)
  segments = split(line, segment, "::")
  if (segments < 2) next
  if (segment[1] == "crate" || segment[1] == "self" || segment[1] == "super") target = library(file)
  else if (segment[1] ~ /^gandr_/) target = segment[1]
  else next
  uses++
  use_file[uses] = file
  use_target[uses] = target
  use_last[uses] = segment[segments]
  use_alias[uses] = (alias == "" ? segment[segments] : alias)
  use_public[uses] = public
}
END {
  do {
    added = 0
    for (u = 1; u <= uses; u++) {
      if (!use_public[u]) continue
      crate = library(use_file[u])
      if (use_last[u] == "*") {
        if (use_target[u] == crate) continue
        for (key in provider) {
          split(key, pair, SUBSEP)
          if (pair[1] == use_target[u]) pending[crate SUBSEP pair[2]] = 1
        }
        for (key in arena) {
          split(key, pair, SUBSEP)
          if (pair[1] == use_target[u]) arena_pending[crate SUBSEP pair[2]] = 1
        }
      } else {
        if ((use_target[u] SUBSEP use_last[u]) in provider) pending[crate SUBSEP use_alias[u]] = 1
        if ((use_target[u] SUBSEP use_last[u]) in arena) arena_pending[crate SUBSEP use_alias[u]] = 1
      }
    }
    for (key in arena_pending) {
      if (!(key in arena)) {
        arena[key] = 1
        added = 1
      }
      delete arena_pending[key]
    }
    for (key in pending) {
      if (!(key in provider)) {
        provider[key] = 1
        added = 1
      }
      delete pending[key]
    }
  } while (added)
  for (key in provider) {
    split(key, pair, SUBSEP)
    names_of[pair[1]] = (pair[1] in names_of) ? names_of[pair[1]] "|" pair[2] : pair[2]
    providers++
  }
  for (i = 1; i <= owned; i++) named[own[i]] = 1
  for (u = 1; u <= uses; u++) {
    if (use_last[u] == "*") {
      if (!(use_target[u] in names_of)) continue
      count = split(names_of[use_target[u]], listed, "|")
      for (i = 1; i <= count; i++) named[use_file[u] SUBSEP listed[i]] = 1
    } else if ((use_target[u] SUBSEP use_last[u]) in provider) {
      named[use_file[u] SUBSEP use_alias[u]] = 1
    }
  }
  for (key in named) {
    split(key, pair, SUBSEP)
    files_of[pair[2]] = (pair[2] in files_of) ? files_of[pair[2]] ", \"" pair[1] "\"" : "\"" pair[1] "\""
    if (!(pair[1] in seen)) { seen[pair[1]] = 1; files++ }
  }
  for (local_name in files_of) emit(fill(ENVIRON["USES"], local_name, local_name, "", "[" files_of[local_name] "]"))
  # The files where a name stands for the arena: its own file, and each file
  # that imports it, a re-export of it, or a glob of a crate that has one.
  for (i = 1; i <= owned; i++) {
    split(own[i], pair, SUBSEP)
    if ((library(pair[1]) SUBSEP pair[2]) in arena) arena_file[pair[1]] = 1
  }
  for (u = 1; u <= uses; u++) {
    if (use_last[u] == "*") {
      for (key in arena) {
        split(key, pair, SUBSEP)
        if (pair[1] == use_target[u]) arena_file[use_file[u]] = 1
      }
    } else if ((use_target[u] SUBSEP use_last[u]) in arena) {
      arena_file[use_file[u]] = 1
    }
  }
  for (file in arena_file) arena_files = (arena_files == "") ? "\"" file "\"" : arena_files ", \"" file "\""
  if (ENVIRON["ROLLBACKS"] != "" && arena_files != "") {
    printf "%s\n", fill(ENVIRON["ROLLBACK_RULES"], "", "", "", "[" arena_files "]") > ENVIRON["ROLLBACKS"]
  }
  for (crate in names_of) {
    emit(fill(ENVIRON["QUALIFIED"], crate, names_of[crate], crate, "[\"**\"]"))
    if (!(crate in directory)) continue
    emit(fill(ENVIRON["QUALIFIED"], crate "-own", names_of[crate], "crate|self|super", "[\"crates/" directory[crate] "/**\"]"))
  }
  printf "%d providers, %d files named one\n", providers, files > "/dev/stderr"
}'

uses=$(<"$region/templates/uses.yml")
qualified=$(<"$region/templates/qualified.yml")
rollback_rules=$(<"$region/templates/rollbacks.yml")
brands > "$scratch/before"
round=0
previous=
while :; do
  round=$((round + 1))
  (( round <= ${CODEMOD_ROUNDS:-32} )) || { echo "codemod-region: the rounds do not settle in ${CODEMOD_ROUNDS:-32}" >&2; exit 1; }
  fixpoint "$region/sgconfig.yml" '^holder-(takes|parameters)' || true
  ast-grep scan --config "$region/sgconfig.yml" --filter '^holder-name$' --json=stream "${paths[@]}" \
    | jq -r '"\(.file)\t\(.metaVariables.single.NAME.text)"' | sort > "$scratch/defined"
  { rg --no-heading --with-filename --no-line-number --type rust \
    '^[[:space:]]*(pub(\([^)]*\))?[[:space:]]+)?use[[:space:]]' "${paths[@]}" || true; } | sort > "$scratch/uses"
  counts=$(SEED_CRATE=$seed_crate SEED_NAMES=$seed_names USES=$uses QUALIFIED=$qualified \
    ARENA=$arena ROLLBACKS=${arena:+$rollback_set/rules/rollbacks.yml} ROLLBACK_RULES=$rollback_rules \
    awk "$names_awk" "$scratch/defined" "$scratch/uses" 2>&1 > "$rule_set/rules/uses.yml")
  signature=$(md5sum < "$rule_set/rules/uses.yml")
  changed=0
  if fixpoint "$rule_set/sgconfig.yml" '.'; then changed=1; fi
  printf 'round %s: %s; files changed: %s\n' "$round" "$counts" "$( ((changed)) && echo yes || echo no)"
  [[ $changed == 1 || $signature != "$previous" ]] || break
  previous=$signature
done
fixpoint "$region/sgconfig.yml" '^(impl-|trait-impl-)' || true
fixpoint "$region/sgconfig.yml" '^fn-' || true
rollbacks=
if [[ -s $rollback_set/rules/rollbacks.yml ]]; then
  matches() {
    ast-grep scan --config "$rollback_set/sgconfig.yml" --filter "$1" --json=stream "${paths[@]}"
  }
  speculations=$(matches '^rollback-speculation$' | jq -s length)
  transactions=$(matches '^rollback-transaction$' | jq -s length)
  fixpoint "$rollback_set/sgconfig.yml" '^rollback-(speculation|transaction)$' || true
  mapfile -t left < <(matches '^rollback-left$' | jq -r '"\(.file):\(.range.start.line + 1)"' | sort)
  rollbacks="; rollbacks that take a fork: $speculations speculations and $transactions transactions; rollbacks left for the hand: ${#left[@]}"
  printf 'rollbacks of %s%s\n' "$arena" "$rollbacks"
  (( ${#left[@]} == 0 )) || printf '  left: %s\n' "${left[@]}"
fi
(( dry_run )) || cargo fmt --all
brands > "$scratch/after"
printf 'brands added, by crate:\n'
join -a 2 -e 0 -o 0,1.2,2.2 "$scratch/before" "$scratch/after" | awk '$3 != $2 { printf "%6d %s\n", $3 - $2, $1 }' | sort -rn
(( ! dry_run )) || printf 'dry run: settled in %s rounds%s; the tree is as it was\n' "$round" "$rollbacks"
