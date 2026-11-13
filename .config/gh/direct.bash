#!/usr/bin/env bash
# A read the change adds is direct when its file does not source the wrapper
# before the call (#6253).
#
# Usage: direct.bash <base> [head]
#
# A read is a call the wrapper would cache. A file sources the wrapper when
# a line above the call sources budget.bash, or stack.bash, deps.bash or
# stall.bash, which source it. In a task file the source must stand in the
# same task. The wrapper's own file is not direct.
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

added_lines() {
  git diff -U0 "$base" "$head" -- "$1" | awk '
    /^@@ / {
      if (match($0, /\+([0-9]+)/)) start = substr($0, RSTART + 1, RLENGTH - 1) + 0
      next
    }
    /^\+\+\+/ { next }
    /^\+/ {
      printf "%d\t%s\n", start, substr($0, 2)
      start++
    }
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

failed=0
while IFS= read -r file; do
  [[ -n $file ]] || continue
  [[ $file == */budget.bash || $file == */calls.toml ]] && continue
  while IFS=$'\t' read -r n text; do
    [[ $text =~ ^[[:space:]]*# ]] && continue
    [[ $text =~ ^[[:space:]]*description[[:space:]]*= ]] && continue
    is_read "$text" || continue
    if ! sourced_before "$file" "$n"; then
      printf '%s:%s: a read the change adds does not source the wrapper before the call\n' "$file" "$n" >&2
      failed=1
    fi
  done < <(added_lines "$file")
done < <(git diff --name-only --diff-filter=ACMR "$base" "$head" -- .config .github | grep -E '\.(bash|sh|toml|ya?ml)$' || true)
exit "$failed"
