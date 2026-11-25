#!/usr/bin/env bash
# The repository paths that a light check of the gate reads, as its task and
# the programs it runs name them (#6895). `check:gate-scope` holds each row of
# the table's `reads` to them (`reads.jq`).
#
# The walk starts from the task's `run` text. It follows each script and each
# jq program that the text names under the tree, each module that a program
# includes or imports, and each task that the text runs through `mise run`. A
# comment names no read, and nor does a task named in backquotes, as a hint in
# a message is. A path with a variable reads the directory before the
# variable, and a glob reads the directory before its first `*`. A line that
# lists or searches the tree and names no path of it reads the whole tree,
# `.`, which no row names. A program that runs Cargo reads the workspace: its
# manifest, its lock, its configuration and every crate.
#
# The walk reads what a program names, not what it computes. A program that
# reads a path it builds from data, such as each crate that a ledger rows,
# names that path in its row by hand. The integration cycle runs every check,
# so a row that misses such a path keeps a stale verdict until the cycle.
#
# Usage: reads.bash <check>...
# Output: one JSON object a line, `{check, path}`, each path once per check.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
# A run entry is a script, or an object that runs another task. A task reads
# the file that defines it.
tasks=$(mise tasks ls --json | jq -c --arg root "$root/" 'map({key: .name, value: {run: ([.run[]? | if type == "string" then . else "mise run \(.task)" end] | join("\n")), source: (.source // "" | ltrimstr($root))}}) | from_entries')
# The tree's first segments: each directory, and each file at the root. A
# path in a program's text starts with one of them.
mapfile -t tops < <(git ls-files | awk -F/ '{ print (NF > 1 ? $1 "/" : $1) }' | sort -u)
dirs=() files=()
for top in "${tops[@]}"; do
  escaped=${top%/}
  escaped=${escaped//./\\.}
  if [[ $top == */ ]]; then dirs+=("$escaped"); else files+=("$escaped"); fi
done
alternation() {
  local IFS='|'
  echo "$*"
}
edge='(^|[^A-Za-z0-9_./-])'
# A directory reads with a path below it, or alone in quotes, as a pathspec.
path_pattern="$edge($(alternation "${dirs[@]}"))(/[A-Za-z0-9_.*/-]*|['\"])|$edge($(alternation "${files[@]}"))[A-Za-z0-9_.-]*"
declare -A top_file=()
for top in "${tops[@]}"; do [[ $top == */ ]] || top_file[$top]=1; done

# A path with `.` and `..` segments, resolved against the root, in `REPLY`.
normal() {
  local IFS=/ part trail=
  local -a out=()
  for part in $1; do
    case $part in
      '' | .) ;;
      ..) ((${#out[@]})) && unset 'out[${#out[@]}-1]' ;;
      *) out+=("$part") ;;
    esac
  done
  [[ $1 == */ && ${#out[@]} -gt 0 ]] && trail=/
  REPLY="${out[*]}$trail"
}

# A program's text with its comments out, and its own directory written in
# for each variable that holds it or a path from it: `$1` is the text, `$2`
# the directory. A variable takes `cd <path> && pwd`, or the path itself.
resolved() {
  local text=$1 dir=$2 name value
  text=$(sed -E -e '/^[[:space:]]*#/d' -e 's/[[:space:]]#[[:space:]].*$//' <<< "$text")
  # shellcheck disable=SC2016 # the program's own text, not an expansion
  text=${text//'${BASH_SOURCE[0]%/*}'/$dir}
  # shellcheck disable=SC2016 # the program's own text, not an expansion
  text=${text//'$(dirname "${BASH_SOURCE[0]}")'/$dir}
  local quoted=${dir//./\\.}
  while read -r name value; do
    [[ -n $name ]] || continue
    normal "$value"
    value=${REPLY:-.}
    text=$(sed -E -e "s#\\\$\\{$name\\}#$value#g" -e "s#\\\$$name([^A-Za-z0-9_]|\$)#$value\\1#g" <<< "$text")
  done < <(sed -nE \
    -e "s#^[[:space:]]*(local[[:space:]]+)?([A-Za-z_]+)=\"?\\\$\\(cd \"?(${quoted}[^\"&)]*)\"? && pwd\\)\"?[[:space:]]*\$#\\2 \\3#p" \
    -e "s#^[[:space:]]*(local[[:space:]]+)?([A-Za-z_]+)=\"?(${quoted}(/[^\" ]*)?)\"?[[:space:]]*\$#\\2 \\3#p" <<< "$text")
  # The root of the tree, by a variable that holds it, by the working
  # directory or by Git's `:/` pathspec, reads as no prefix.
  sed -E -e 's#\$\{?(root|PWD)\}?/##g' -e 's#\$\(git rev-parse --show-toplevel\)/##g' -e "s#(['\" ]):/#\\1#g" <<< "$text"
}

declare -A task_text=() task_source=()
while IFS= read -r -d '' name && IFS= read -r -d '' text && IFS= read -r -d '' source; do
  task_text[$name]=$text
  task_source[$name]=$source
done < <(jq -j 'to_entries[] | .key, "\u0000", .value.run, "\u0000", .value.source, "\u0000"' <<< "$tasks")

# What one program names, once for each program: `named` holds the paths it
# reads, `next` the programs and tasks to walk from it, each a line.
declare -A named=() next=()
scan() {
  local item=$1 text dir name kind module as token reads='' walk=''
  case $item in
    task:*)
      text=${task_text[${item#task:}]:-}
      dir=.
      [[ -n ${task_source[${item#task:}]:-} ]] && reads+=${task_source[${item#task:}]}$'\n'
      ;;
    */*)
      text=$(< "$item")
      dir=${item%/*}
      ;;
    *)
      text=$(< "$item")
      dir=.
      ;;
  esac
  text=$(resolved "$text" "$dir")
  # The tasks that the text runs, never one in backquotes.
  while read -r name; do
    [[ -n $name ]] && walk+="task:$name"$'\n'
  done < <(grep -oE '(^|[^`A-Za-z0-9_-])mise run( --quiet)? [A-Za-z0-9_:-]+' <<< "$text" | awk '{ print $NF }')
  # The modules that a jq program includes or imports, from its directory.
  # A module of data is read, and holds no program to walk.
  if [[ $item == *.jq ]]; then
    # shellcheck disable=SC2016 # `$` names a jq variable, not an expansion
    while read -r kind module as; do
      if [[ $kind == import && $as == \$* ]]; then module+=.json; else module+=.jq; fi
      [[ -f $dir/$module ]] || continue
      normal "$dir/$module"
      reads+=$REPLY$'\n'
      [[ $module == *.jq ]] && walk+=$REPLY$'\n'
    done < <(grep -oE '^(include|import) "[^"]+"( as [$A-Za-z_]+)?' <<< "$text" | sed -E 's/^(include|import) "([^"]+)"( as ([$A-Za-z_]+))?/\1 \2 \4/')
  fi
  # A line that lists or searches the tree with no path of it.
  if grep -E 'git (ls-files|grep)|\brg\b|\bfind \.' <<< "$text" | grep -qvE "$path_pattern"; then
    reads+=.$'\n'
  fi
  # Cargo reads the workspace whatever the line names.
  if grep -qE '(^|[^A-Za-z0-9_-])cargo [a-z]' <<< "$text"; then
    reads+=$'Cargo.toml\nCargo.lock\n.cargo/\ncrates/\n'
  fi
  while read -r token; do
    token=${token%%\**}
    token=${token%[\'\"]}
    if [[ $token != */* ]]; then
      if [[ -d $token ]]; then
        token+=/
      else
        [[ -n ${top_file[$token]:-} ]] || continue
      fi
    elif [[ -d $token ]]; then
      token=${token%/}/
    elif [[ $token != */ && ! -e $token ]]; then
      token=${token%/*}/
    fi
    normal "$token"
    [[ -z $REPLY || $REPLY == target/* ]] && continue
    reads+=$REPLY$'\n'
    case $REPLY in
      *.bash | *.sh | *.jq | *.awk | *.py) [[ -f $REPLY ]] && walk+=$REPLY$'\n' ;;
    esac
  done < <(grep -oE "$path_pattern" <<< "$text" | sed -E 's/^[^A-Za-z0-9_.]//')
  named[$item]=$reads
  next[$item]=$walk
}

for check in "$@"; do
  if [[ -z ${task_text[$check]+set} ]]; then
    echo "reads: no task $check" >&2
    exit 2
  fi
  declare -A walked=() found=()
  queue=("task:$check")
  while ((${#queue[@]})); do
    item=${queue[0]}
    queue=("${queue[@]:1}")
    [[ -n ${walked[$item]:-} ]] && continue
    walked[$item]=1
    [[ -n ${named[$item]+set} ]] || scan "$item"
    while IFS= read -r path; do
      [[ -n $path ]] && found[$path]=1
    done <<< "${named[$item]}"
    while IFS= read -r follow; do
      [[ -n $follow ]] && queue+=("$follow")
    done <<< "${next[$item]}"
  done
  for path in "${!found[@]}"; do
    printf '{"check":"%s","path":"%s"}\n' "$check" "$path"
  done
  unset walked found
done
