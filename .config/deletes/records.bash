#!/usr/bin/env bash
# Writes the evidence records of each package to `<out>`, as the record run
# of `check.bash` builds them at `<tree>` (#6823). Each package's records come
# from a cache when its key and its inputs outside the key are the same as
# when they were built. Each other package builds in a `cargo dylint` run of
# its own, and that run writes the entry of the package (#6861).
#
# One entry holds the record files of one package: each file whose name
# starts with the package's directory, as `crates_<dir>_`. A run also writes
# the records of the package's workspace dependencies, and the entry keeps
# none of them.
#
# The key is the SHA-256 of a manifest. The manifest has one line for each
# input that a record of the package reads:
#   - the git tree of the directory of each workspace package that the
#     package's units reach, in Cargo's unit graph of the package alone;
#   - each unit that the package's units reach: its package, its target, its
#     mode, its features, its platform and its profile. A run over several
#     packages unifies their features, and the key of each package would then
#     depend on the others. So each package has a unit graph and a run of its
#     own, and its key is the same in each check that touches it;
#   - the blobs of `Cargo.lock`, `Cargo.toml`, `.cargo/config.toml`,
#     `rust-toolchain.toml`, `mise.toml` and `mise.lock`;
#   - the policy configuration of the run with its records' directory taken
#     out, its flags, and the blob of each file of the tree that it names;
#   - the rustflags of the run, `rustc -vV`, `cargo -V`, the version of
#     `cargo-dylint`, and each Cargo configuration outside the tree;
#   - the value of `DYLINT_LIBRARY_PATH`, since `--lib` searches it first.
#     The lint library comes from the revision that `Cargo.toml` pins, and
#     that revision pins its sources, its `Cargo.lock` and its toolchain. Its
#     bytes differ from one target directory to the next, so the key holds
#     its source and not its digest.
# At the head, a temporary index takes `git add -A`. So each tree comes from
# the working state, with each edit that no commit holds yet.
#
# The inputs outside the key come from the run that writes the entry. The
# dep-info of each workspace unit names each file that rustc reads: an
# `include_str!` file, a `#[path]` module and each `env!` variable. The
# stdout of each build script names its `rerun-if-changed` paths and its
# `rerun-if-env-changed` variables. A path in a hashed directory, in the
# target directory, in Cargo's home or in the toolchain needs no line. A
# path elsewhere in the tree adds its git object. A directory that a build
# script names also adds the names in its parent directory, since the build
# script lists that directory. A path outside the tree adds the SHA-256 of
# its content, and a variable adds its value. The entry keeps the list and
# the digest of the values. A read takes the entry only when the list gives
# the same digest at its own tree.
#
# Some inputs stay out by reason. The C toolchain builds the C parts of
# registry crates and reads no workspace source. The git configuration
# reaches only the git dependencies, which `Cargo.lock` pins. A proc macro
# that reads a file by its own `fs` call, and not through `tracked_path`, is
# outside rustc's dep-info. No crate of the workspace does so today.
#
# A write fills a directory of a temporary name in the cache, then renames
# it to the key in one `rename` call. A reader sees a whole entry or none. A
# second writer of a key removes its own directory. A temporary directory
# older than one hour is a crash's leftover, and the next write removes it.
# When the working state moves during a run, the run writes no entry, since
# its records would then sit under the key of a different content.
# The cache lives at `${XDG_CACHE_HOME:-$HOME/.cache}/gandr/deletes-records`,
# or at `GANDR_DELETES_RECORDS`. A read touches its entry, and past 2 GiB the
# entries with the oldest touch leave first.
#
# Usage: records.bash <tree> <target> <out> <package>=<directory>...
# `<directory>` is the package's directory in the tree. Prints one line with
# the count of hits and of builds. Exits 2 when the records do not build.
#
# The cases (`records-cases.bash`) source this file for its functions.
set -euo pipefail
records_here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
records_bound_kib=$((2 * 1024 * 1024))
records_rustflags=$'--cfg=quenchant_compiler_policy\x1f-Zalways-encode-mir\x1f-Zinline-mir=no'

# A copy on one host clones.
records_clone() {
  if [[ $(uname -s) == Darwin ]]; then cp -c "$@"; else cp --reflink=auto "$@"; fi
}

records_sha() {
  local digest _
  if command -v sha256sum > /dev/null; then read -r digest _ < <(sha256sum); else read -r digest _ < <(shasum -a 256); fi
  echo "$digest"
}

# The git object of each path read on stdin, in the root tree
# `$records_root`: one `[<prefix> ]<path> <object>` line each, with `missing`
# for a path that the root tree lacks. One `git cat-file` reads them all.
records_objects() {
  local prefix=${1:+$1 } paths=() line i=0
  mapfile -t paths
  (( ${#paths[@]} )) || return 0
  while IFS= read -r line; do
    if [[ $line == *" missing" ]]; then line=missing; fi
    echo "$prefix${paths[i]} $line"
    i=$((i + 1))
  done < <(printf "$records_root:%s\n" "${paths[@]}" | git -C "$records_tree" cat-file --batch-check='%(objectname)')
}

# Runs `$@` in the tree with the environment of the record run.
records_run() {
  (cd "$records_tree" \
    && CARGO_INCREMENTAL=0 CARGO_TARGET_DIR="$records_target" \
      CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=dylint-link CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=dylint-link \
      CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER=dylint-link CARGO_TARGET_X86_64_APPLE_DARWIN_LINKER=dylint-link \
      CARGO_ENCODED_RUSTFLAGS=$records_rustflags DYLINT_TOML=$records_config DYLINT_RUSTFLAGS=$records_flags \
      "$@")
}

# Sets the root tree of the working state of the tree: a temporary index
# takes `git add -A`, and `git write-tree` gives the root.
records_snapshot() {
  local index
  index=$(git -C "$records_tree" rev-parse --path-format=absolute --git-path index)
  rm -f "$records_work/index"
  if [[ -f $index ]]; then records_clone "$index" "$records_work/index"; fi
  GIT_INDEX_FILE=$records_work/index git -C "$records_tree" add -A
  records_root=$(GIT_INDEX_FILE=$records_work/index git -C "$records_tree" write-tree)
}

# Sets the tree, the target, the work directory, the root tree of the
# working state, and the policy of the run. `$1` the tree, `$2` the target.
records_open() {
  records_tree=$(cd "$1" && pwd -P)
  mkdir -p "$2"
  records_target=$(cd "$2" && pwd -P)
  records_work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-records.XXXXXX")
  records_snapshot
  records_config=$("$records_here/policy.bash" "$records_tree" "$records_work/records")
  records_flags=$("$records_here/policy.bash" --flags "$records_tree" "$records_work/records")
}

# The lines of the manifest that every package of the tree shares.
records_fixed() {
  local path value dir seen=" "
  echo "scheme 2"
  printf '%s\n' Cargo.lock Cargo.toml .cargo/config.toml rust-toolchain.toml mise.toml mise.lock | records_objects blob
  echo "policy $(awk -v tree="$records_tree" '!/^evidence_directory = / {
      while ((at = index($0, tree)) > 0) $0 = substr($0, 1, at - 1) "<tree>" substr($0, at + length(tree))
      print }' <<< "$records_config" | records_sha)"
  echo "flags $records_flags"
  while IFS= read -r value; do
    value=${value#"$records_tree"/}
    if [[ $value == */* && $value != /* && $value != *' '* ]]; then echo "$value"; fi
  done < <(awk '{ while (match($0, /"[^"]*"/)) { print substr($0, RSTART + 1, RLENGTH - 2); $0 = substr($0, RSTART + RLENGTH) } }' <<< "$records_config" | sort -u) \
    | records_objects named | awk '$NF != "missing"'
  echo "rustflags ${records_rustflags//$'\x1f'/ }"
  value=$(cd "$records_tree" && rustc -vV)
  echo "rustc ${value//$'\n'/ }"
  echo "cargo $(cd "$records_tree" && cargo -V)"
  echo "cargo-dylint $(cd "$records_tree" && cargo dylint --version)"
  # Cargo reads the configuration of each directory above the tree.
  dir=${records_tree%/*}
  while :; do
    for path in "$dir/.cargo/config.toml" "$dir/.cargo/config"; do
      if [[ -f $path ]]; then echo "cargo-config $path $(records_sha < "$path")"; seen+="$path "; fi
    done
    [[ -n $dir ]] || break
    dir=${dir%/*}
  done
  path=${CARGO_HOME:-$HOME/.cargo}/config.toml
  if [[ -f $path && $seen != *" $path "* ]]; then echo "cargo-config $path $(records_sha < "$path")"; fi
  if value=$(printenv DYLINT_LIBRARY_PATH); then echo "library-path set $(records_sha <<< "$value")"; else echo "library-path unset"; fi
}

# Cargo's unit graph of the run over package `$1`, as JSON. A second
# argument names the features to turn on, joined by commas.
records_units() {
  local args=(-p "$1")
  [[ -z ${2:-} ]] || args+=(--features "$2")
  records_run cargo check --unit-graph -Z unstable-options "${args[@]}" --all-targets --locked
}

# The features that the targets of package `$1` require, joined by commas,
# or nothing. The tree's own lint passes decide, as for its policy: a tree
# whose passes turn on these features carries `.config/policy/required.bash`,
# and the passes of an older tree build no target that requires a feature.
records_required() {
  local script=$records_tree/.config/policy/required.bash
  [[ -x $script ]] || return 0
  records_run cargo metadata --no-deps --locked --format-version 1 | "$script" --package "$1"
}

# What the units of the package in directory `$2` reach in the unit graph
# `$1`: `{units: [<manifest line>], dirs: [<directory>], packages: [<id>]}`.
records_closure() {
  jq -c --arg ws "path+file://$records_tree/" --arg dir "$2" '
    def reach($g; $start):
      {seen: (reduce $start[] as $i ({}; .[$i | tostring] = true)), todo: $start}
      | until(.todo == [];
          .todo[0] as $i | .todo |= .[1:]
          | reduce ($g.units[$i].dependencies[].index) as $d (.;
              if .seen[$d | tostring] then . else .seen[$d | tostring] = true | .todo += [$d] end))
      | .seen | keys | map(tonumber);
    . as $g
    | [$g.units | to_entries[] | select(.value.pkg_id | startswith($ws + $dir + "#")) | .key] as $roots
    | if $roots == [] then error("the unit graph holds no unit of " + $dir) else . end
    | [reach($g; $roots)[] | $g.units[.]] as $reached
    | {units: ($reached | map("unit "
          + (.pkg_id | if startswith($ws) then "workspace:" + ltrimstr($ws) else . end)
          + " " + (.target.kind | join(",")) + " " + .target.name + " " + .mode
          + " [" + (.features | join(",")) + "] " + (.platform // "host") + " " + (.profile | tojson)) | unique),
       dirs: ($reached | map(.pkg_id | select(startswith($ws)) | ltrimstr($ws) | split("#")[0]) | unique),
       packages: ($reached | map(.pkg_id) | unique)}' "$1"
}

# The manifest of one package: the shared lines `$1`, then its closure `$2`.
records_manifest() {
  local line dirs=()
  printf '%s\n' "$1"
  while IFS= read -r line; do
    if [[ $line == "dir "* ]]; then dirs+=("${line#dir }"); else echo "$line"; fi
  done < <(jq -r '.units[], (.dirs[] | "dir " + .)' <<< "$2")
  if (( ${#dirs[@]} )); then printf '%s\n' "${dirs[@]}" | records_objects tree; fi
}

# Resolves each line of the inputs outside the key, read on stdin, at the
# tree: `path <in tree>`, `names <directory in tree>`, `file <outside>` and
# `env <name>`. Prints each with its value.
records_resolve() {
  local lines=() line kind arg value
  local -A objects=()
  mapfile -t lines
  (( ${#lines[@]} )) || return 0
  while read -r arg value; do objects[$arg]=$value; done \
    < <(printf '%s\n' "${lines[@]}" | awk '$1 == "path" || $1 == "names" { print $2 }' | records_objects)
  for line in "${lines[@]}"; do
    read -r kind arg <<< "$line"
    case $kind in
      path) value=${objects[$arg]} ;;
      names)
        if [[ ${objects[$arg]} == missing ]]; then value=missing
        else value=$(git -C "$records_tree" ls-tree --name-only "${objects[$arg]}" | records_sha); fi ;;
      file) if [[ -f $arg ]]; then value=$(records_sha < "$arg"); else value=missing; fi ;;
      env)
        # A build script can name a variable that no shell variable can hold,
        # as `CC_aarch64-apple-darwin`, so `printenv` reads it.
        [[ $arg =~ ^[^=[:space:]-][^=[:space:]]*$ ]] || { echo "check:deletes: $arg names no variable" >&2; return 2; }
        if printenv "$arg" > /dev/null; then value="set $(printenv "$arg" | records_sha)"; else value='unset'; fi ;;
      *) echo "check:deletes: $kind is no kind of input" >&2; return 2 ;;
    esac
    echo "$kind $arg $value"
  done
}

# The inputs outside the key of one package, from the run's messages `$1`
# and the package's closure `$2`. Prints the sorted list. The closure goes
# to `jq` through a pipe: as one argument, the closure of a large package
# passes the bound of 131,072 bytes that Linux sets (#7062).
records_extras() {
  local messages=$1 closure=$2 file stdout package base
  local sysroot cargo_home
  sysroot=$(cd "$records_tree" && rustc --print sysroot)
  cargo_home=${CARGO_HOME:-$HOME/.cargo}
  {
    # The dep-info of each workspace unit that the package reaches.
    jq -rn --slurpfile closure <(printf '%s\n' "$closure") \
      '(reduce $closure[0].packages[] as $p ({}; .[$p] = true)) as $reached | inputs | select(.reason == "compiler-artifact" and $reached[.package_id] and (.package_id | startswith("path+file://"))) | .filenames[]' \
      "$messages" | while IFS= read -r file; do
        base=$(basename "$file")
        base=${base%.rmeta}
        base=${base%.rlib}
        file=$(dirname "$file")/${base#lib}.d
        [[ -f $file ]] || continue
        awk -v tree="$records_tree" '
          /^# env-dep:/ { name = substr($0, 11); sub(/=.*/, "", name); print "env", name; next }
          /:$/ && !/: / && !/^#/ { path = substr($0, 1, length($0) - 1); print "dep", (path ~ /^\// ? path : tree "/" path) }' "$file"
      done
    # The stdout of each build script that the package reaches.
    jq -rn --slurpfile closure <(printf '%s\n' "$closure") \
      '(reduce $closure[0].packages[] as $p ({}; .[$p] = true)) as $reached | inputs | select(.reason == "build-script-executed" and $reached[.package_id]) | [.package_id, .out_dir] | @tsv' \
      "$messages" | while IFS=$'\t' read -r package file; do
        stdout=$(dirname "$file")/run/stdout
        [[ -f $stdout ]] || stdout=$(dirname "$file")/output
        [[ -f $stdout ]] || continue
        base=
        if [[ $package == "path+file://"* ]]; then base=${package#path+file://}; base=${base%%#*}; fi
        awk -v base="$base" '
          { line = $0; sub(/^cargo::?/, "", line) }
          line ~ /^rerun-if-env-changed=/ { print "env", substr(line, 22); next }
          line ~ /^rerun-if-changed=/ {
            path = substr(line, 18)
            if (path !~ /^\//) { if (base == "") next; path = base "/" path }
            print "run", path }' "$stdout"
      done
  } | awk -v tree="$records_tree" -v target="$records_target" -v home="$cargo_home" -v sysroot="$sysroot" \
      -v dirs="$(jq -r '.dirs | join(" ")' <<< "$closure")" '
    function clean(path,    parts, n, i, out, k) {
      n = split(path, parts, "/"); k = 0
      for (i = 1; i <= n; i++) {
        if (parts[i] == "" || parts[i] == ".") continue
        if (parts[i] == "..") { if (k > 0) k--; continue }
        out[++k] = parts[i]
      }
      path = ""
      for (i = 1; i <= k; i++) path = path "/" out[i]
      return path
    }
    BEGIN { n = split(dirs, hashed, " ") }
    $1 == "env" {
      name = $2
      if (name ~ /^(CARGO_|DYLINT_)/ || name ~ /^(OUT_DIR|TARGET|HOST|NUM_JOBS|OPT_LEVEL|PROFILE|DEBUG|RUSTC|RUSTDOC|RUSTC_LINKER|RUSTC_WRAPPER|RUSTC_WORKSPACE_WRAPPER)$/) next
      print "env", name; next
    }
    {
      path = clean($2)
      if (index(path, target "/") == 1 || index(path, home "/") == 1 || index(path, sysroot "/") == 1) next
      if (index(path, tree "/") != 1 && path != tree) { print "file", path; next }
      relative = substr(path, length(tree) + 2)
      # A directory that a build script names: the script lists its parent.
      if ($1 == "run") print "dir", relative
      for (i = 1; i <= n; i++) if (relative == hashed[i] || index(relative, hashed[i] "/") == 1) next
      if (relative != "") print "path", relative
    }' | while read -r kind arg; do
      if [[ $kind == dir ]]; then
        [[ -d $records_tree/$arg ]] || continue
        if [[ $arg == */* ]]; then echo "names ${arg%/*}"; fi
      else
        echo "$kind $arg"
      fi
    done | sort -u
}

# Whether the entry of key `$1` holds a whole entry, its manifest equals the
# file `$2`, and its inputs outside the key resolve to its digest.
records_valid() {
  local entry=$records_cache/$1
  [[ -d $entry/files && -f $entry/manifest && -f $entry/extras && -f $entry/extras.sha ]] || return 1
  cmp -s "$entry/manifest" "$2" || return 1
  [[ $(records_resolve < "$entry/extras" | records_sha) == "$(< "$entry/extras.sha")" ]]
}

# Takes the entry of key `$1` into `$2` when it is valid against the
# manifest file `$3`. Fails otherwise.
records_take() {
  local entry=$records_cache/$1 out=$2 files
  records_valid "$1" "$3" || return 1
  shopt -s nullglob
  files=("$entry"/files/*)
  shopt -u nullglob
  if (( ${#files[@]} )); then records_clone "${files[@]}" "$out/"; fi
  touch "$entry"
}

# Writes the entry of key `$1`: the files of `$2` whose names start with `$3`,
# the manifest file `$4` and the inputs outside the key, the file `$5`. A
# valid entry under the key stays, and the writer removes its own directory.
# A stale one leaves first, by a rename.
records_put() {
  local key=$1 records=$2 prefix=$3 manifest=$4 extras=$5 tmp files
  tmp=$records_cache/.tmp-$BASHPID-$key
  rm -rf "$tmp"
  mkdir -p "$tmp/files"
  shopt -s nullglob
  files=("$records/$prefix"*)
  shopt -u nullglob
  if (( ${#files[@]} )); then records_clone "${files[@]}" "$tmp/files/"; fi
  cp "$manifest" "$tmp/manifest"
  cp "$extras" "$tmp/extras"
  records_resolve < "$extras" | records_sha > "$tmp/extras.sha"
  if [[ -e $records_cache/$key ]]; then
    if records_valid "$key" "$manifest"; then rm -rf "$tmp"; return 0; fi
    perl -e 'rename($ARGV[0], $ARGV[1]) or exit 1' "$records_cache/$key" "$records_cache/.tmp-$BASHPID-stale-$key" 2> /dev/null \
      && rm -rf "$records_cache/.tmp-$BASHPID-stale-$key"
  fi
  perl -e 'rename($ARGV[0], $ARGV[1]) or exit 1' "$tmp" "$records_cache/$key" 2> /dev/null || rm -rf "$tmp"
}

# Removes each crash's leftover, and the entries with the oldest touch past
# the bound.
records_evict() {
  local size entry used
  find "$records_cache" -mindepth 1 -maxdepth 1 -name '.tmp-*' -mmin +60 -exec rm -rf {} +
  size=$(du -sk "$records_cache" | awk '{ print $1 }')
  while IFS= read -r entry; do
    (( size > records_bound_kib )) || break
    used=$(du -sk "$records_cache/$entry" | awk '{ print $1 }')
    rm -rf "${records_cache:?}/$entry"
    size=$((size - used))
  done < <(ls -1tr "$records_cache")
}

# Builds the records of package `$1` into `$records_work/records`, with the
# run's messages in `$records_work/messages.json`. A second argument names
# the features to turn on, as for `records_units`. The run first takes the
# package's own artifacts out of the check targets that `cargo dylint` keeps
# under `dylint/target/<toolchain>` of the records target. The run of a
# package that depends on it builds its library there, a fresh unit gives no
# record, and the entry would then hold no library unit (#7092).
records_build() {
  local dir args=(-p "$1")
  [[ -z ${2:-} ]] || args+=(--features "$2")
  rm -rf "$records_work/records"
  mkdir -p "$records_work/records"
  : > "$records_work/dylint.log"
  for dir in "$records_target"/dylint/target/*/; do
    [[ -d $dir ]] || continue
    records_run cargo clean --quiet -p "$1" --target-dir "$dir" 2>> "$records_work/dylint.log" || return
  done
  records_run cargo dylint --lib quenchant_dylints -- "${args[@]}" --all-targets --locked --quiet --message-format=json \
    > "$records_work/messages.json" 2>> "$records_work/dylint.log"
}

records_main() {
  local tree=${1:?usage: records.bash <tree> <target> <out> <package>=<directory>...}
  local target=${2:?usage: records.bash <tree> <target> <out> <package>=<directory>...}
  local out=${3:?usage: records.bash <tree> <target> <out> <package>=<directory>...}
  shift 3
  (( $# )) || return 0
  records_cache=${GANDR_DELETES_RECORDS:-${XDG_CACHE_HOME:-$HOME/.cache}/gandr/deletes-records}
  mkdir -p "$out" "$records_cache"
  records_open "$tree" "$target"
  trap 'rm -rf "$records_work"' EXIT
  local names=() dirs=() features=() pair i fixed key root prefix files missed=() hits=0
  for pair in "$@"; do names+=("${pair%%=*}"); dirs+=("${pair#*=}"); done
  fixed=$(records_fixed)
  for i in "${!names[@]}"; do
    features[i]=$(records_required "${names[i]}") \
      || { echo "check:deletes: no metadata of ${names[i]} at $records_tree" >&2; return 2; }
    records_units "${names[i]}" "${features[i]}" > "$records_work/units-$i.json" 2> "$records_work/units.log" \
      || { echo "check:deletes: no unit graph of ${names[i]} at $records_tree:" >&2; tail -n 20 "$records_work/units.log" >&2; return 2; }
    records_closure "$records_work/units-$i.json" "${dirs[i]}" > "$records_work/closure-$i"
    records_manifest "$fixed" "$(< "$records_work/closure-$i")" > "$records_work/manifest-$i"
    key=$(records_sha < "$records_work/manifest-$i")
    if records_take "$key" "$out" "$records_work/manifest-$i"; then hits=$((hits + 1)); else missed+=("$i"); fi
  done
  root=$records_root
  for i in "${missed[@]}"; do
    records_build "${names[i]}" "${features[i]}" \
      || { echo "check:deletes: the records of ${names[i]} at $records_tree do not build:" >&2; tail -n 20 "$records_work/dylint.log" >&2; return 2; }
    prefix=$(tr '/' '_' <<< "${dirs[i]}")_
    shopt -s nullglob
    files=("$records_work/records/$prefix"*)
    shopt -u nullglob
    if (( ${#files[@]} )); then records_clone "${files[@]}" "$out/"; fi
    # An edit of the tree during the run gives records of one content under
    # the key of another, so the run then writes no entry.
    records_snapshot
    if [[ $records_root != "$root" ]]; then
      echo "check:deletes: $records_tree moved during the record run of ${names[i]}, so the cache keeps no entry of it" >&2
      continue
    fi
    records_extras "$records_work/messages.json" "$(< "$records_work/closure-$i")" > "$records_work/extras-$i"
    key=$(records_sha < "$records_work/manifest-$i")
    records_put "$key" "$records_work/records" "$prefix" "$records_work/manifest-$i" "$records_work/extras-$i"
  done
  if (( ${#missed[@]} )); then records_evict; fi
  echo "records of $records_tree: $hits from the cache, ${#missed[@]} built"
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then records_main "$@"; fi
