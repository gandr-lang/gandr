#!/usr/bin/env bash
# The inputs of a check that compiles a scope, and their digest. A verdict is
# a function of what its check reads. So a record of the verdict binds the
# digest of those inputs, and a reader computes the digest from the tree that
# it holds. Two trees with one digest share one record, so a merge group whose
# base moved reads the record of its pull request's gate.
# - see: #7684, `verdict.bash`
#
# The inputs of a scope, each a path and its object at a commit:
#   - each crate of the scope and of its dependency closure, by the object of
#     its directory. The closure follows each kind of dependency on a crate of
#     the workspace;
#   - the manifest of each crate of the workspace. The workspace unifies
#     features, so a crate outside the closure can turn on a feature inside
#     it;
#   - each file of the workspace's configuration that `inputs.json` names;
#   - each file outside its crate that a crate of the closure reads, as
#     `inputs.json` names it;
#   - each path of the check's own definition, as `verdicts.json` names it,
#     and the task's definition as `mise` reads it;
#   - for each grep of the check that `verdicts.json` names, the list of the
#     files that hold its pattern. A task that greps each crate reads only
#     that list, so a change of another file keeps its record.
# A path that a commit does not hold stands as `absent`.
#
# Cargo writes the files that each unit read, in its dep-info. After a check
# runs, `depinfo` reads those files. It refuses each file of the tree that the
# inputs of the scope do not hold, by its path. So a gap of `inputs.json`
# shows at the first run that meets it.
#
# Usage:
#   inputs.bash list <commit> <scope> <check>
#     Prints the inputs of <check> over <scope> at <commit>, one per line: the
#     path, a tab and its object.
#   inputs.bash digest <commit> <scope> <check>
#     Prints the SHA-256 of that list.
#   inputs.bash depinfo <stamp> <scope> <directory>...
#     Reads each dep-info file under each <directory> that is newer than the
#     file <stamp>. Exits 1 and names each file of the tree that a unit of a
#     workspace crate read and that the inputs of <scope> do not hold.
#
# `GATE_INPUTS_TABLE` names another table than `inputs.json`, and
# `GATE_INPUTS_TASK` gives the task's definition, for the cases
# (`verdict-cases.bash`), whose scratch repository holds no task.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git rev-parse --show-toplevel)
table=${GATE_INPUTS_TABLE:-$here/inputs.json}

# The crates of the workspace, each with its directory and the crates of the
# workspace that it depends on, by any kind of dependency.
crates() {
  cargo metadata --format-version 1 --no-deps --locked --manifest-path "$root/Cargo.toml" \
    | jq -c --arg root "$root/" '
      [.packages[] | {name, dir: (.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml"))}] as $members
      | ($members | map(.name)) as $names
      | [.packages[] | {name, dir: (.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml")),
          deps: ([.dependencies[].name | select(IN($names[]))] | unique)}]'
}

# The paths that the inputs of <check> over <scope> name, one per line, from
# the crates of the workspace on stdin. A path that ends in `/` names a
# directory.
paths() {
  local scope=$1 check=$2
  jq -r --arg scope "$scope" --arg check "$check" --slurpfile table "$table" --slurpfile checks "$here/verdicts.json" '
    . as $crates
    | ($crates | map({(.name): .}) | add) as $by
    | ([$scope | splits(" +")] | . as $words
        | [range(0; length) | select($words[.] == "--exclude") | $words[. + 1]]) as $excluded
    | [$crates[].name | select(IN($excluded[]) | not)] as $scoped
    | {set: $scoped, work: $scoped}
    | until(.work | length == 0;
        .work[0] as $n
        | ($by[$n].deps - .set) as $new
        | .set += $new | .work = .work[1:] + $new)
    | .set as $closure
    | [($closure[] | $by[.].dir + "/"),
       ($crates[] | .dir + "/Cargo.toml"),
       $table[0].workspace[],
       ($closure[] | ($table[0].outside[.] // [])[]),
       ($checks[0].checks[$check].inputs // [])[]]
    | unique[]'
}

# The objects of the paths on stdin at <commit>, as `path<TAB>object`.
objects() {
  local commit=$1
  awk -v commit="$commit" '{ path = $0; sub(/\/$/, "", path); print commit ":" path }' \
    | git cat-file --batch-check='%(objectname)' \
    | paste - <(cat "$paths_file") \
    | awk -F'\t' '{ object = $1; if (object ~ / missing$/) object = "absent"; print $2 "\t" object }'
}

# The list of <check> over <scope> at <commit>.
list() {
  local commit=$1 scope=$2 check=$3 task
  paths_file=$(mktemp)
  trap 'rm -f "$paths_file"' RETURN
  crates | paths "$scope" "$check" > "$paths_file"
  objects "$commit" < "$paths_file"
  # The task's own definition: what it runs, its environment, its tools and
  # its dependencies, as `mise` reads them in this checkout. The source path
  # and the directory name the checkout, so the definition omits them.
  task=${GATE_INPUTS_TASK:-$(mise tasks info "$check" --json | jq -c -S '{run, env, tools, depends}')}
  task=$(printf '%s' "$task" | sha256sum | cut -c1-64)
  printf 'task:%s\t%s\n' "$check" "$task"
  jq -r --arg check "$check" '(.checks[$check].greps // [])[] | "\(.pattern)\t\(.in)"' "$here/verdicts.json" \
    | while IFS=$'\t' read -r pattern within; do
        found=$({ git grep -l -e "$pattern" "$commit" -- "$within" || true; } \
          | awk -v prefix="$commit:" 'index($0, prefix) == 1 { $0 = substr($0, length(prefix) + 1) } { print }' \
          | sha256sum | cut -c1-64)
        printf 'grep:%s:%s\t%s\n' "$within" "$pattern" "$found"
      done
}

case ${1:-} in
  list)
    (( $# == 4 )) || { echo 'usage: inputs.bash list <commit> <scope> <check>' >&2; exit 2; }
    list "$2" "$3" "$4"
    ;;
  digest)
    (( $# == 4 )) || { echo 'usage: inputs.bash digest <commit> <scope> <check>' >&2; exit 2; }
    list "$2" "$3" "$4" | LC_ALL=C sort | sha256sum | cut -c1-64
    ;;
  depinfo)
    (( $# >= 4 )) || { echo 'usage: inputs.bash depinfo <stamp> <scope> <directory>...' >&2; exit 2; }
    stamp=$2
    scope=$3
    shift 3
    crates=$(crates)
    allowed=$(paths "$scope" none <<< "$crates")
    # Two kinds of file of this run name the files that a unit of a workspace
    # crate reads. They are rustc's dep-info and the `rerun-if-changed` lines
    # of a build script's run. A relative path of the dep-info is relative to
    # the root, where cargo runs rustc. A relative path of a build script is
    # relative to its crate. A path that the tree does not hold is no input of
    # the tree: a case builds its own scratch crate there.
    refused=$(for directory in "$@"; do
        [[ -d $directory ]] || continue
        find "$directory" \( -name '*.d' -o -path '*/run/stdout' \) -newer "$stamp" -print0
      done | xargs -0 -r awk -v root="$root/" '
        function emit(kind, p) {
          if (index(p, root) == 1) print FILENAME "\troot\t" substr(p, length(root) + 1)
          else if (p !~ /^\// && p != "") print FILENAME "\t" kind "\t" p
        }
        FILENAME ~ /\/run\/stdout$/ {
          if ($0 ~ /^cargo::?rerun-if-changed=/) { p = $0; sub(/^cargo::?rerun-if-changed=/, "", p); emit("crate", p) }
          next
        }
        /^#/ || /^$/ { next }
        {
          line = $0
          gsub(/\\ /, "\001", line)
          if (line ~ /:$/) { line = substr(line, 1, length(line) - 1) }
          else { sub(/^[^ ]*: */, "", line) }
          n = split(line, parts, " ")
          for (i = 1; i <= n; i++) { p = parts[i]; gsub("\001", " ", p); emit("root", p) }
        }' \
      | jq -R -r --slurpfile crates <(printf '%s\n' "$crates") --rawfile allowed <(printf '%s\n' "$allowed") '
        def norm: reduce (split("/")[]) as $s ([];
          if $s == ".." and length > 0 and .[-1] != ".." then .[:-1] elif $s == "." or $s == "" then . else . + [$s] end) | join("/");
        ($crates[0] | map({(.name): .dir}) | add) as $dir
        | ($allowed | split("\n") | map(select(length > 0))) as $allowed
        | split("\t") as [$file, $kind, $raw]
        | ($file | capture("/build/(?<crate>[^/]+)/[^/]+/(out/[a-z0-9_]+-[0-9a-f]{16}\\.d|run/stdout)$")) as $unit
        | select($dir[$unit.crate] != null)
        | (if $kind == "crate" then $dir[$unit.crate] + "/" + $raw else $raw end | norm) as $path
        | select(($path | startswith("target/") or startswith("../")) | not)
        | select(any($allowed[]; . as $a | $a == $path or $a == $path + "/" or (($a | endswith("/")) and ($path | startswith($a)))) | not)
        | "\($unit.crate)\t\($path)"' \
      | LC_ALL=C sort -u \
      | while IFS=$'\t' read -r crate path; do
          if [[ -e $root/$path ]]; then printf '%s\t%s\n' "$crate" "$path"; fi
        done)
    if [[ -n $refused ]]; then
      while IFS=$'\t' read -r crate path; do
        echo "inputs: $crate read $path, which the inputs of its scope do not hold; name it under \`outside.$crate\` in .config/gate-scope/inputs.json (#7684)" >&2
      done <<< "$refused"
      exit 1
    fi
    echo "inputs: each file of the tree that the run read is an input of its scope" >&2
    ;;
  *)
    echo 'usage: inputs.bash list|digest|depinfo …' >&2
    exit 2
    ;;
esac
