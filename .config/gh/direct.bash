#!/usr/bin/env bash
# Every GitHub read of a task file goes through the wrapper, and so does a
# read that the change adds to another workflow script (#6253).
#
# Usage: direct.bash <base> [head]
#
# A read is a call the wrapper would cache. A file sources the wrapper when
# a line above the call sources budget.bash, or stack.bash, deps.bash or
# stall.bash, which source it. In a task file the source must stand in the
# same task. The check reads each line of each task file under
# `.config/mise/tasks/` at the head, changed or not, and the lines that the
# change adds to each other script. The wrapper's own file is not direct. A
# file that the change renames adds only the lines that its source at the base
# lacks.
set -euo pipefail
base=${1:?usage: direct.bash <base> [head]}
head=${2:-HEAD}
word=$(printf '%s%s' g h)

is_read() {
  local line=$1 sub arg
  [[ $line =~ (^|[^A-Za-z0-9_./$-])${word}[[:space:]]+([a-z][a-z-]*)([[:space:]]+([A-Za-z][A-Za-z-]*))? ]] || return 1
  sub=${BASH_REMATCH[2]}
  arg=${BASH_REMATCH[4]:-}
  case $sub in
    search) return 0 ;;
    pr) [[ $arg =~ ^(view|list|checks|diff|status)$ ]] ;;
    issue) [[ $arg =~ ^(view|list|status)$ ]] ;;
    run) [[ $arg =~ ^(view|list)$ ]] ;;
    repo | release | label) [[ $arg =~ ^(view|list)$ ]] ;;
    api) api_read "$line" ;;
    *) return 1 ;;
  esac
}

api_read() {
  local line=$1
  if [[ $line =~ [[:space:]]graphql([[:space:]]|$) ]]; then
    [[ $line != *mutation* ]]
    return
  fi
  if [[ $line =~ (-X[[:space:]]*|--method[[:space:]=]+)(POST|PATCH|PUT|DELETE) ]]; then
    return 1
  fi
  if [[ $line =~ (^|[[:space:]])(-f|-F|--field|--raw-field|--input)([[:space:]=]|[^[:space:]]) ]]; then
    return 1
  fi
  return 0
}

# Each line of `$1` at the head that the change adds, with its number. A
# renamed file is read against `$2`, its path at the base, so a line that it
# keeps reads as kept. A read that takes the place of a read of the same
# command, in the same hunk, reads as kept too: the change edits its
# arguments, as a rename of a workflow does, and adds no call.
added_lines() {
  git diff -M -U0 "$base" "$head" -- ${2:+"$2"} "$1" | awk -v word="$word" '
    function kind(text,    k) {
      if (!match(text, word "[ \t]+[a-z][a-z-]*([ \t]+[A-Za-z][A-Za-z-]*)?")) return ""
      k = substr(text, RSTART, RLENGTH)
      gsub(/[ \t]+/, " ", k)
      return k
    }
    function flush(    i, k) {
      for (i = 1; i <= count; i++) {
        k = kind(added[i])
        if (k != "" && dropped[k] > 0) {
          dropped[k]--
          continue
        }
        printf "%d\t%s\n", at[i], added[i]
      }
      count = 0
      split("", dropped)
    }
    /^@@ / {
      flush()
      hunk = 1
      if (match($0, /\+([0-9]+)/)) start = substr($0, RSTART + 1, RLENGTH - 1) + 0
      next
    }
    !hunk { next }
    /^-/ {
      k = kind(substr($0, 2))
      if (k != "") dropped[k]++
      next
    }
    /^\+/ {
      added[++count] = substr($0, 2)
      at[count] = start
      start++
    }
    END { flush() }
  '
}

sourced_before() {
  local toml=0
  [[ $1 == *.toml ]] && toml=1
  git show "$head:$1" | awk -v line="$2" -v toml="$toml" '
    BEGIN { start = 1 }
    toml && /^\[(tasks\.)?"[^"]+"\]/ && NR < line { start = NR; found = 0 }
    NR >= start && NR < line && $0 !~ /^[ \t]*#/ && /source/ && /(budget|stack|deps|stall)\.bash/ { found = 1 }
    END { exit found ? 0 : 1 }
  '
}

# The lines of the task file `$1` at the head above which no line of the same
# task sources the wrapper, numbered: one pass over the file.
unsourced_lines() {
  git show "$head:$1" | awk '
    /^\[(tasks\.)?"[^"]+"\]/ { found = 0 }
    !found { printf "%d\t%s\n", NR, $0 }
    $0 !~ /^[ \t]*#/ && /source/ && /(budget|stack|deps|stall)\.bash/ { found = 1 }
  '
}

# Each read of the numbered lines on stdin that no source of the wrapper
# stands above, refused as `$2` with its file `$1` and its line. With `$3`
# set, each read's source is looked up above it in the file.
judge() {
  local file=$1 what=$2 lookup=${3:-} n text
  while IFS=$'\t' read -r n text; do
    [[ $text =~ ^[[:space:]]*# ]] && continue
    [[ $text =~ ^[[:space:]]*description[[:space:]]*= ]] && continue
    is_read "$text" || continue
    if [[ -n $lookup ]] && sourced_before "$file" "$n"; then continue; fi
    printf '%s:%s: %s does not source the wrapper before the call\n' "$file" "$n" "$what" >&2
    failed=1
  done
}

failed=0
while IFS= read -r file; do
  [[ -n $file ]] || continue
  judge "$file" 'a read of a task file' < <(unsourced_lines "$file")
done < <(git ls-tree -r --name-only "$head" -- .config/mise/tasks | grep -E '\.toml$' || true)
while IFS=$'\t' read -r status from file; do
  [[ -n $from ]] || continue
  if [[ $status != R* ]]; then
    file=$from
    from=""
  fi
  [[ $file =~ \.(bash|sh|toml|ya?ml)$ ]] || continue
  [[ $file == */budget.bash || $file == */calls.toml || $file == .config/mise/tasks/*.toml ]] && continue
  judge "$file" 'a read the change adds' lookup < <(added_lines "$file" "$from")
done < <(git diff -M --name-status --diff-filter=ACMR "$base" "$head" -- .config .github)
exit "$failed"
